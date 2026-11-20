// Forge — a GitHub-compatible git forge in one dependency-free TypeScript file.
//
// Four surfaces share one in-memory store: git smart HTTP (protocol v2 and v0),
// the REST v3 API, the GraphQL v4 API and an MCP endpoint. Objects pushed over git
// are the same objects the contents API writes and GraphQL reads; refs, issues and
// pull requests are shared the same way. Standard library only: node:http for the
// server, node:crypto for SHA-1 object ids, node:zlib for pack compression.
//
// Authored for the make.fun "github-core-clone-01" bounty (ArulAdiSanjaya).

import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash, randomBytes } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------------------
// Constants and shared state

/** The login the shop token names (the trial scenario's viewer). */
const VIEWER_LOGIN = 'adaiversen';
/** The default branch every repository is born with. */
const DEFAULT_BRANCH = 'main';
/** The bearer token the suite presents; unset only in ad-hoc local runs. */
const SHOP_TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
/** Version string for GET /api/v3/meta and the git agent capability. */
const FORGE_VERSION = '1.0.0';
const AGENT = `forge/${FORGE_VERSION}`;
const ZERO_OID = '0000000000000000000000000000000000000000';
const JSON_TYPE = 'application/json; charset=utf-8';
/** Fixed epoch base for forge-authored commits; a counter keeps them increasing. */
const COMMIT_EPOCH = 1_735_689_600;

let requestCounter = 0;
let repoIdCounter = 100;
let issueIdCounter = 1000;
let commentIdCounter = 1000;
let commitClock = 0;

type GitObjectType = 'commit' | 'tree' | 'blob' | 'tag';

interface GitObject {
  type: GitObjectType;
  data: Buffer;
}

/** The one object store: content-addressed, shared by every repo and surface. */
const objectStore = new Map<string, GitObject>();

interface TreeEntry {
  mode: string;
  name: string;
  oid: string;
}

interface IssueRec {
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: string[];
  comments: Array<{ id: number; body: string }>;
}

interface PullRec {
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  head: string;
  base: string;
  merged: boolean;
  mergedAt: string | null;
  mergeCommitSha: string | null;
}

interface Repo {
  id: number;
  name: string;
  owner: string | null;
  description: string;
  isPrivate: boolean;
  defaultBranch: string;
  refs: Map<string, string>;
  labels: Map<string, { name: string; color: string }>;
  issues: Map<number, IssueRec>;
  pulls: Map<number, PullRec>;
  nextNumber: number;
}

/** Repositories by name; the owner is adopted from the first owner path that addresses the repo. */
const repos = new Map<string, Repo>();

function createRepoRec(name: string, description: string, isPrivate: boolean): Repo {
  const repo: Repo = {
    id: repoIdCounter++,
    name,
    owner: null,
    description,
    isPrivate,
    defaultBranch: DEFAULT_BRANCH,
    refs: new Map(),
    labels: new Map(),
    issues: new Map(),
    pulls: new Map(),
    nextNumber: 1,
  };
  repos.set(name, repo);
  return repo;
}

/** Find a repo by owner/name, adopting the owner on first address; a foreign owner reads as absent. */
function findRepo(owner: string, name: string): Repo | null {
  const repo = repos.get(name);
  if (repo === undefined) return null;
  if (repo.owner === null) repo.owner = owner;
  if (repo.owner !== owner) return null;
  return repo;
}

// ---------------------------------------------------------------------------
// Git object model

function hashObject(type: GitObjectType, data: Buffer): string {
  const header = Buffer.from(`${type} ${data.length}\0`, 'utf8');
  return createHash('sha1').update(header).update(data).digest('hex');
}

function storeObject(type: GitObjectType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!objectStore.has(oid)) objectStore.set(oid, { type, data });
  return oid;
}

function getObject(oid: string): GitObject | undefined {
  return objectStore.get(oid);
}

interface CommitRec {
  tree: string;
  parents: string[];
  message: string;
}

function parseCommit(data: Buffer): CommitRec {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const head = split === -1 ? text : text.slice(0, split);
  const message = split === -1 ? '' : text.slice(split + 2);
  let tree = '';
  const parents: string[] = [];
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
  }
  return { tree, parents, message };
}

function buildCommitData(tree: string, parents: string[], message: string): Buffer {
  const stamp = COMMIT_EPOCH + commitClock++;
  const identity = `${VIEWER_LOGIN} <${VIEWER_LOGIN}@example.invalid> ${stamp} +0000`;
  const lines = [`tree ${tree}`];
  for (const parent of parents) lines.push(`parent ${parent}`);
  lines.push(`author ${identity}`, `committer ${identity}`, '', message);
  return Buffer.from(lines.join('\n'), 'utf8');
}

function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let offset = 0;
  while (offset < data.length) {
    const space = data.indexOf(0x20, offset);
    const mode = data.subarray(offset, space).toString('ascii');
    const nul = data.indexOf(0x00, space + 1);
    const name = data.subarray(space + 1, nul).toString('utf8');
    const oid = data.subarray(nul + 1, nul + 21).toString('hex');
    entries.push({ mode, name, oid });
    offset = nul + 21;
  }
  return entries;
}

/** Git's tree order: names compared byte-wise, directories as if suffixed with '/'. */
function treeSortKey(entry: TreeEntry): string {
  return entry.mode === '40000' ? `${entry.name}/` : entry.name;
}

function buildTreeData(entries: TreeEntry[]): Buffer {
  const sorted = [...entries].sort((a, b) => (treeSortKey(a) < treeSortKey(b) ? -1 : treeSortKey(a) > treeSortKey(b) ? 1 : 0));
  const parts: Buffer[] = [];
  for (const entry of sorted) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\0`, 'utf8'));
    parts.push(Buffer.from(entry.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

/** Flatten a tree into path -> entry, recursing into subtrees. */
function flattenTree(treeOid: string, prefix: string, out: Map<string, TreeEntry>): void {
  const tree = getObject(treeOid);
  if (tree === undefined || tree.type !== 'tree') return;
  for (const entry of parseTree(tree.data)) {
    const path = prefix === '' ? entry.name : `${prefix}/${entry.name}`;
    if (entry.mode === '40000') flattenTree(entry.oid, path, out);
    else out.set(path, entry);
  }
}

/** Rebuild nested trees from a flat path -> entry map; returns the root tree oid. */
function buildTreeFromFlat(flat: Map<string, TreeEntry>): string {
  interface Node {
    files: TreeEntry[];
    dirs: Map<string, Node>;
  }
  const root: Node = { files: [], dirs: new Map() };
  for (const [path, entry] of flat) {
    const segments = path.split('/');
    let node = root;
    for (let i = 0; i < segments.length - 1; i++) {
      let next = node.dirs.get(segments[i]!);
      if (next === undefined) {
        next = { files: [], dirs: new Map() };
        node.dirs.set(segments[i]!, next);
      }
      node = next;
    }
    node.files.push({ mode: entry.mode, name: segments[segments.length - 1]!, oid: entry.oid });
  }
  const build = (node: Node): string => {
    const entries: TreeEntry[] = [...node.files];
    for (const [name, child] of node.dirs) entries.push({ mode: '40000', name, oid: build(child) });
    return storeObject('tree', buildTreeData(entries));
  };
  return build(root);
}

/** The flat file map of a commit (empty map when the commit is unknown). */
function commitFiles(commitOid: string): Map<string, TreeEntry> {
  const out = new Map<string, TreeEntry>();
  const commit = getObject(commitOid);
  if (commit === undefined || commit.type !== 'commit') return out;
  flattenTree(parseCommit(commit.data).tree, '', out);
  return out;
}

/** Resolve any object id to the commit it points at (through annotated tags), or null. */
function peelToCommit(oid: string): string | null {
  let current = oid;
  for (let depth = 0; depth < 16; depth++) {
    const object = getObject(current);
    if (object === undefined) return null;
    if (object.type === 'commit') return current;
    if (object.type === 'tag') {
      const match = /^object ([0-9a-f]{40})$/m.exec(object.data.toString('utf8'));
      if (match === null) return null;
      current = match[1]!;
      continue;
    }
    return null;
  }
  return null;
}

/** All commits reachable from `tips` following parents (optionally not past `shallow` commits). */
function commitClosure(tips: readonly string[], shallow: ReadonlySet<string> = new Set()): Set<string> {
  const seen = new Set<string>();
  const stack: string[] = [];
  for (const tip of tips) {
    const commit = peelToCommit(tip);
    if (commit !== null) stack.push(commit);
  }
  while (stack.length > 0) {
    const oid = stack.pop()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    if (shallow.has(oid)) continue;
    const object = getObject(oid);
    if (object === undefined || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) stack.push(parent);
  }
  return seen;
}

/** Whether `ancestor` is reachable from `descendant` through parent links. */
function isAncestor(ancestor: string, descendant: string): boolean {
  if (ancestor === descendant) return true;
  return commitClosure([descendant]).has(ancestor);
}

/** The best common ancestor of two commits, or null (BFS from both sides). */
function mergeBase(a: string, b: string): string | null {
  const ancestorsA = commitClosure([a]);
  if (ancestorsA.has(b)) return b;
  if (commitClosure([b]).has(a)) return a;
  const seen = new Set<string>();
  const queue: string[] = [b];
  while (queue.length > 0) {
    const oid = queue.shift()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    if (ancestorsA.has(oid)) return oid;
    const object = getObject(oid);
    if (object === undefined || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) queue.push(parent);
  }
  return null;
}

/** Add a commit's tree closure (trees and blobs, recursively) to `into`. */
function addTreeClosure(treeOid: string, into: Set<string>): void {
  if (into.has(treeOid)) return;
  const tree = getObject(treeOid);
  if (tree === undefined || tree.type !== 'tree') return;
  into.add(treeOid);
  for (const entry of parseTree(tree.data)) {
    if (entry.mode === '40000') addTreeClosure(entry.oid, into);
    else into.add(entry.oid);
  }
}

// ---------------------------------------------------------------------------
// pkt-line framing

type Pkt = { kind: 'data'; payload: Buffer } | { kind: 'flush' } | { kind: 'delim' } | { kind: 'end' };

function pktLine(payload: Buffer | string): Buffer {
  const body = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const header = Buffer.from((body.length + 4).toString(16).padStart(4, '0'), 'ascii');
  return Buffer.concat([header, body]);
}

const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');

/** Parse a pkt-line stream; null when the framing is malformed. */
function parsePkts(buffer: Buffer, offset = 0): { packets: Pkt[]; rest: number } | null {
  const packets: Pkt[] = [];
  let pos = offset;
  while (pos < buffer.length) {
    if (pos + 4 > buffer.length) return null;
    const header = buffer.subarray(pos, pos + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(header)) return null;
    const length = parseInt(header, 16);
    if (length === 0) {
      packets.push({ kind: 'flush' });
      pos += 4;
      // Everything after the first flush is not pkt-line framing (a pack, in receive-pack).
      return { packets, rest: pos };
    }
    if (length === 1) {
      packets.push({ kind: 'delim' });
      pos += 4;
      continue;
    }
    if (length === 2) {
      packets.push({ kind: 'end' });
      pos += 4;
      continue;
    }
    if (length < 4 || length > 65520 || pos + length > buffer.length) return null;
    packets.push({ kind: 'data', payload: buffer.subarray(pos + 4, pos + length) });
    pos += length;
  }
  return { packets, rest: pos };
}

/** One sideband packet: band byte + payload, pkt-framed. */
function sidebandPkt(band: number, payload: Buffer): Buffer {
  return pktLine(Buffer.concat([Buffer.from([band]), payload]));
}

// ---------------------------------------------------------------------------
// Pack files

const PACK_TYPE_IDS: Record<string, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const PACK_ID_TYPES: Record<number, GitObjectType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

function writePack(oids: readonly string[]): Buffer {
  const parts: Buffer[] = [];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(oids.length, 8);
  parts.push(header);
  for (const oid of oids) {
    const object = getObject(oid);
    if (object === undefined) continue;
    const typeId = PACK_TYPE_IDS[object.type]!;
    let size = object.data.length;
    const first = (typeId << 4) | (size & 0x0f);
    size >>= 4;
    const bytes: number[] = [];
    if (size > 0) {
      bytes.push(first | 0x80);
      while (size > 0) {
        let byte = size & 0x7f;
        size >>= 7;
        if (size > 0) byte |= 0x80;
        bytes.push(byte);
      }
    } else {
      bytes.push(first);
    }
    parts.push(Buffer.from(bytes));
    parts.push(deflateSync(object.data));
  }
  const body = Buffer.concat(parts);
  const trailer = createHash('sha1').update(body).digest();
  return Buffer.concat([body, trailer]);
}

/**
 * Inflate exactly one zlib stream starting at `offset`; reports where it ended.
 * Node's zlib does not expose how many input bytes a stream consumed, so the end is
 * found by binary search: the smallest prefix that inflates cleanly is the stream.
 */
function inflateOne(buffer: Buffer, offset: number): { data: Buffer; next: number } {
  let lo = 1;
  let hi = buffer.length - offset;
  let best = -1;
  while (lo <= hi) {
    const mid = (lo + hi) >> 1;
    try {
      inflateSync(buffer.subarray(offset, offset + mid));
      best = mid;
      hi = mid - 1;
    } catch {
      lo = mid + 1;
    }
  }
  if (best < 0) throw new Error('corrupt zlib stream in pack');
  return { data: inflateSync(buffer.subarray(offset, offset + best)), next: offset + best };
}

/** Apply a git delta (the copy/insert opcode stream) to a base object. */
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let pos = 0;
  const readVarint = (): number => {
    let value = 0;
    let shift = 0;
    for (;;) {
      const byte = delta[pos++]!;
      value |= (byte & 0x7f) << shift;
      shift += 7;
      if ((byte & 0x80) === 0) break;
    }
    return value;
  };
  readVarint(); // base size
  const targetSize = readVarint();
  const out: Buffer[] = [];
  while (pos < delta.length) {
    const op = delta[pos++]!;
    if (op & 0x80) {
      let copyOffset = 0;
      let copySize = 0;
      for (let i = 0; i < 4; i++) if (op & (1 << i)) copyOffset |= delta[pos++]! << (8 * i);
      for (let i = 0; i < 3; i++) if (op & (0x10 << i)) copySize |= delta[pos++]! << (8 * i);
      if (copySize === 0) copySize = 0x10000;
      out.push(base.subarray(copyOffset, copyOffset + copySize));
    } else if (op !== 0) {
      out.push(delta.subarray(pos, pos + op));
      pos += op;
    } else {
      throw new Error('delta opcode 0');
    }
  }
  const result = Buffer.concat(out);
  if (result.length !== targetSize) throw new Error('delta size mismatch');
  return result;
}

interface PackEntry {
  headerStart: number;
  type: GitObjectType | null; // null while a delta is unresolved
  data: Buffer; // plain object bytes, or the delta stream while unresolved
  baseOid?: string;
  baseHeaderStart?: number;
}

/**
 * Parse a pack into the object store. Returns an error string, or null on success.
 * Plain objects are the norm; ofs/ref deltas are resolved iteratively for completeness.
 */
async function ingestPack(pack: Buffer): Promise<string | null> {
  try {
    if (pack.length < 12 + 20 || pack.subarray(0, 4).toString('ascii') !== 'PACK') return 'not a pack file';
    const count = pack.readUInt32BE(8);
    let offset = 12;
    const entries: PackEntry[] = [];
    for (let i = 0; i < count; i++) {
      const headerStart = offset;
      let byte = pack[offset++]!;
      const typeId = (byte >> 4) & 0x07;
      let size = byte & 0x0f;
      let shift = 4;
      while (byte & 0x80) {
        byte = pack[offset++]!;
        size |= (byte & 0x7f) << shift;
        shift += 7;
      }
      if (typeId === 6) {
        // ofs-delta: a negative offset back to the base object's header start.
        let baseByte = pack[offset++]!;
        let baseOffset = baseByte & 0x7f;
        while (baseByte & 0x80) {
          baseByte = pack[offset++]!;
          baseOffset = ((baseOffset + 1) << 7) | (baseByte & 0x7f);
        }
        const inflated = inflateOne(pack, offset);
        offset = inflated.next;
        entries.push({ headerStart, type: null, data: inflated.data, baseHeaderStart: headerStart - baseOffset });
      } else if (typeId === 7) {
        const baseOid = pack.subarray(offset, offset + 20).toString('hex');
        offset += 20;
        const inflated = inflateOne(pack, offset);
        offset = inflated.next;
        entries.push({ headerStart, type: null, data: inflated.data, baseOid });
      } else {
        const type = PACK_ID_TYPES[typeId];
        if (type === undefined) return `unknown pack object type ${typeId}`;
        const inflated = inflateOne(pack, offset);
        offset = inflated.next;
        if (inflated.data.length !== size) return 'pack object size mismatch';
        entries.push({ headerStart, type, data: inflated.data });
      }
    }
    const byHeader = new Map<number, PackEntry>();
    for (const entry of entries) byHeader.set(entry.headerStart, entry);
    let unresolved = entries.filter((entry) => entry.type === null);
    for (const entry of entries) {
      if (entry.type !== null) storeObject(entry.type, entry.data);
    }
    let guard = 0;
    while (unresolved.length > 0 && guard++ < entries.length + 2) {
      const still: PackEntry[] = [];
      for (const entry of unresolved) {
        let base: GitObject | undefined;
        if (entry.baseOid !== undefined) base = getObject(entry.baseOid);
        else if (entry.baseHeaderStart !== undefined) {
          const baseEntry = byHeader.get(entry.baseHeaderStart);
          if (baseEntry !== undefined && baseEntry.type !== null) base = { type: baseEntry.type, data: baseEntry.data };
        }
        if (base === undefined) {
          still.push(entry);
          continue;
        }
        entry.data = applyDelta(base.data, entry.data);
        entry.type = base.type;
        storeObject(entry.type, entry.data);
      }
      unresolved = still;
    }
    if (unresolved.length > 0) return 'delta base missing from pack and store';
    return null;
  } catch (err) {
    return err instanceof Error ? err.message : 'pack parse failed';
  }
}

// ---------------------------------------------------------------------------
// HTTP plumbing

function sendJson(res: ServerResponse, status: number, body: unknown, headers: Readonly<Record<string, string>> = {}): void {
  const text = body === undefined ? '' : `${JSON.stringify(body)}\n`;
  res.writeHead(status, {
    'content-type': JSON_TYPE,
    'content-length': Buffer.byteLength(text),
    'x-github-request-id': `forge-${++requestCounter}-${randomBytes(4).toString('hex')}`,
    ...headers,
  });
  res.end(text);
}

function sendRaw(res: ServerResponse, status: number, body: Buffer, contentType: string): void {
  res.writeHead(status, { 'content-type': contentType, 'content-length': body.length, 'cache-control': 'no-store' });
  res.end(body);
}

async function readBody(req: IncomingMessage): Promise<Buffer> {
  const chunks: Buffer[] = [];
  let size = 0;
  for await (const chunk of req) {
    const buffer = chunk as Buffer;
    size += buffer.length;
    if (size > 64 * 1024 * 1024) throw new Error('request body too large');
    chunks.push(buffer);
  }
  return Buffer.concat(chunks);
}

/** The suite's bearer token: exact match when the trial issued one, any bearer otherwise. */
function bearerOk(req: IncomingMessage): boolean {
  const header = req.headers.authorization;
  if (typeof header !== 'string') return false;
  if (SHOP_TOKEN !== '') return header === `Bearer ${SHOP_TOKEN}`;
  return header.startsWith('Bearer ') && header.length > 'Bearer '.length;
}

function notFound(res: ServerResponse): void {
  sendJson(res, 404, { message: 'Not Found' });
}

// ---------------------------------------------------------------------------
// Git smart HTTP

function sortedRefEntries(repo: Repo): Array<[string, string]> {
  return [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
}

/** The commit a tag object peels to (itself for non-tags), or null. */
function peeledOf(oid: string): string | null {
  const object = getObject(oid);
  if (object === undefined) return null;
  if (object.type !== 'tag') return oid;
  return peelToCommit(oid);
}

const UPLOAD_CAPS = `multi_ack_detailed side-band-64k thin-pack ofs-delta shallow agent=${AGENT} symref=HEAD:refs/heads/${DEFAULT_BRANCH}`;
const RECEIVE_CAPS = `report-status side-band-64k delete-refs ofs-delta agent=${AGENT}`;

/** The v0 ref advertisement lines (HEAD first, peeled tag lines after their tag). */
function v0RefLines(repo: Repo, caps: string): Buffer[] {
  const lines: Buffer[] = [];
  const headRef = `refs/heads/${repo.defaultBranch}`;
  const headOid = repo.refs.get(headRef);
  const entries: Array<[string, string]> = [];
  if (headOid !== undefined) entries.push(['HEAD', headOid]);
  for (const entry of sortedRefEntries(repo)) entries.push(entry);
  if (entries.length === 0) {
    lines.push(pktLine(`${ZERO_OID} capabilities^{}\0${caps}\n`));
    return lines;
  }
  entries.forEach(([name, oid], index) => {
    lines.push(pktLine(index === 0 ? `${oid} ${name}\0${caps}\n` : `${oid} ${name}\n`));
    if (name.startsWith('refs/tags/')) {
      const peeled = peeledOf(oid);
      if (peeled !== null && peeled !== oid) lines.push(pktLine(`${peeled} ${name}^{}\n`));
    }
  });
  return lines;
}

function handleInfoRefs(req: IncomingMessage, res: ServerResponse, repo: Repo, url: URL): void {
  const service = url.searchParams.get('service');
  if (service !== 'git-upload-pack' && service !== 'git-receive-pack') {
    sendJson(res, 403, { message: 'unsupported service' });
    return;
  }
  const v2 = (req.headers['git-protocol'] ?? '').toString().includes('version=2');
  if (service === 'git-upload-pack' && v2) {
    const body = Buffer.concat([
      pktLine('version 2\n'),
      pktLine(`agent=${AGENT}\n`),
      pktLine('ls-refs=unborn\n'),
      pktLine('fetch=shallow\n'),
      pktLine('object-format=sha1\n'),
      PKT_FLUSH,
    ]);
    sendRaw(res, 200, body, 'application/x-git-upload-pack-advertisement');
    return;
  }
  const caps = service === 'git-upload-pack' ? UPLOAD_CAPS : RECEIVE_CAPS;
  const body = Buffer.concat([pktLine(`# service=${service}\n`), PKT_FLUSH, ...v0RefLines(repo, caps)]);
  sendRaw(res, 200, body, `application/x-${service}-advertisement`);
}

/** Parse every pkt section in a body (sections end at flush packets). */
function parseAllSections(buffer: Buffer): Pkt[][] | null {
  const sections: Pkt[][] = [];
  let offset = 0;
  while (offset < buffer.length) {
    const parsed = parsePkts(buffer, offset);
    if (parsed === null) return null;
    sections.push(parsed.packets);
    offset = parsed.rest;
    if (parsed.packets.length === 0) break;
    if (parsed.packets[parsed.packets.length - 1]!.kind !== 'flush') break;
  }
  return sections;
}

function dataLines(packets: Pkt[]): string[] {
  const lines: string[] = [];
  for (const packet of packets) {
    if (packet.kind === 'data') lines.push(packet.payload.toString('utf8').replace(/\n$/, ''));
  }
  return lines;
}

function handleLsRefs(res: ServerResponse, repo: Repo, packets: Pkt[]): void {
  // packets: command line, capability lines, delim, argument lines, flush.
  let wantPeel = false;
  let wantSymrefs = false;
  let wantUnborn = false;
  const prefixes: string[] = [];
  let pastDelim = false;
  for (const packet of packets) {
    if (packet.kind === 'delim') {
      pastDelim = true;
      continue;
    }
    if (packet.kind !== 'data' || !pastDelim) continue;
    const line = packet.payload.toString('utf8').replace(/\n$/, '');
    if (line === 'peel') wantPeel = true;
    else if (line === 'symrefs') wantSymrefs = true;
    else if (line === 'unborn') wantUnborn = true;
    else if (line.startsWith('ref-prefix ')) prefixes.push(line.slice('ref-prefix '.length));
  }
  const matches = (name: string): boolean => prefixes.length === 0 || prefixes.some((prefix) => name.startsWith(prefix));
  const headRef = `refs/heads/${repo.defaultBranch}`;
  const headOid = repo.refs.get(headRef);
  const lines: string[] = [];
  if (matches('HEAD')) {
    if (headOid !== undefined) lines.push(`${headOid} HEAD${wantSymrefs ? ` symref-target:${headRef}` : ''}\n`);
    else if (wantUnborn) lines.push(`unborn HEAD${wantSymrefs ? ` symref-target:${headRef}` : ''}\n`);
  }
  for (const [name, oid] of sortedRefEntries(repo)) {
    if (!matches(name)) continue;
    let line = `${oid} ${name}`;
    if (wantPeel) {
      const peeled = peeledOf(oid);
      if (peeled !== null && peeled !== oid) line += ` peeled:${peeled}`;
    }
    lines.push(`${line}\n`);
  }
  const body = Buffer.concat([...lines.map((line) => pktLine(line)), PKT_FLUSH]);
  sendRaw(res, 200, body, 'application/x-git-upload-pack-result');
}

interface FetchSelection {
  send: string[];
  shallow: string[];
  unshallow: string[];
}

/**
 * The objects a fetch transfers: the wants' closure within `deepen` commit generations
 * (unbounded when deepen is null), minus everything the client's haves already cover.
 * Held history stops at the client's shallow boundary commits, as the protocol settles.
 */
function computeFetch(wants: readonly string[], haves: readonly string[], clientShallow: readonly string[], deepen: number | null): FetchSelection {
  const shallowSet = new Set(clientShallow);
  const heldCommits = commitClosure(haves, shallowSet);
  const held = new Set<string>(heldCommits);
  for (const commit of heldCommits) {
    const object = getObject(commit);
    if (object !== undefined && object.type === 'commit') addTreeClosure(parseCommit(object.data).tree, held);
  }

  // Breadth-first by commit generation from the wants (generation 1 = the wants).
  const included = new Set<string>();
  const distance = new Map<string, number>();
  const queue: string[] = [];
  const extraRoots: string[] = [];
  for (const want of wants) {
    const object = getObject(want);
    if (object === undefined) continue;
    if (object.type === 'commit') {
      if (!distance.has(want)) {
        distance.set(want, 1);
        queue.push(want);
      }
    } else {
      extraRoots.push(want);
    }
  }
  while (queue.length > 0) {
    const oid = queue.shift()!;
    const dist = distance.get(oid)!;
    included.add(oid);
    if (deepen !== null && dist >= deepen) continue;
    const object = getObject(oid);
    if (object === undefined || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) {
      if (!distance.has(parent)) {
        distance.set(parent, dist + 1);
        queue.push(parent);
      }
    }
  }
  const includedObjects = new Set<string>(included);
  for (const commit of included) {
    const object = getObject(commit);
    if (object !== undefined && object.type === 'commit') addTreeClosure(parseCommit(object.data).tree, includedObjects);
  }
  for (const root of extraRoots) {
    includedObjects.add(root);
    const object = getObject(root)!;
    if (object.type === 'tag') {
      const target = peelToCommit(root);
      if (target !== null && !included.has(target)) {
        // A tag want pulls its commit's whole history (no depth was negotiated for it).
        for (const commit of commitClosure([target])) {
          includedObjects.add(commit);
          const commitObject = getObject(commit);
          if (commitObject !== undefined && commitObject.type === 'commit') addTreeClosure(parseCommit(commitObject.data).tree, includedObjects);
        }
      }
    } else if (object.type === 'tree') {
      addTreeClosure(root, includedObjects);
    }
  }

  const shallow: string[] = [];
  const unshallow: string[] = [];
  for (const commit of included) {
    const object = getObject(commit);
    if (object === undefined || object.type !== 'commit') continue;
    const parents = parseCommit(object.data).parents;
    const boundary = parents.some((parent) => getObject(parent) !== undefined && !included.has(parent));
    if (boundary) {
      if (!shallowSet.has(commit)) shallow.push(commit);
    } else if (shallowSet.has(commit)) {
      unshallow.push(commit);
    }
  }

  const send = [...includedObjects].filter((oid) => !held.has(oid) && getObject(oid) !== undefined);
  return { send, shallow, unshallow };
}

/** Frame a pack as sideband-1 packets (payload chunks stay under the pkt-line cap). */
function sidebandStream(pack: Buffer): Buffer[] {
  const parts: Buffer[] = [];
  const CHUNK = 65515;
  for (let offset = 0; offset < pack.length; offset += CHUNK) {
    parts.push(sidebandPkt(1, pack.subarray(offset, offset + CHUNK)));
  }
  if (parts.length === 0) parts.push(sidebandPkt(1, Buffer.alloc(0)));
  return parts;
}

function fetchSections(
  selection: FetchSelection,
  haves: readonly string[],
  includeShallowSection: boolean,
): Buffer {
  const parts: Buffer[] = [];
  parts.push(pktLine('acknowledgments\n'));
  const acked = haves.filter((have) => getObject(have) !== undefined);
  if (acked.length === 0) parts.push(pktLine('NAK\n'));
  else for (const have of acked) parts.push(pktLine(`ACK ${have}\n`));
  parts.push(PKT_FLUSH);
  if (includeShallowSection && (selection.shallow.length > 0 || selection.unshallow.length > 0)) {
    parts.push(pktLine('shallow-info\n'));
    for (const oid of selection.shallow) parts.push(pktLine(`shallow ${oid}\n`));
    for (const oid of selection.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
    parts.push(PKT_FLUSH);
  }
  parts.push(pktLine('packfile\n'));
  parts.push(...sidebandStream(writePack(selection.send)));
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

async function handleUploadPack(res: ServerResponse, repo: Repo, body: Buffer): Promise<void> {
  const first = parsePkts(body, 0);
  if (first === null || first.packets.length === 0 || first.packets[0]!.kind !== 'data') {
    sendJson(res, 400, { message: 'malformed pkt-line request' });
    return;
  }
  const firstLine = (first.packets[0] as { payload: Buffer }).payload.toString('utf8').replace(/\n$/, '');

  if (firstLine === 'command=ls-refs') {
    handleLsRefs(res, repo, first.packets);
    return;
  }

  if (firstLine === 'command=fetch') {
    const wants: string[] = [];
    const haves: string[] = [];
    const clientShallow: string[] = [];
    let deepen: number | null = null;
    let pastDelim = false;
    for (const packet of first.packets) {
      if (packet.kind === 'delim') {
        pastDelim = true;
        continue;
      }
      if (packet.kind !== 'data' || !pastDelim) continue;
      const line = packet.payload.toString('utf8').replace(/\n$/, '');
      if (line.startsWith('want ')) wants.push(line.slice(5).trim());
      else if (line.startsWith('have ')) haves.push(line.slice(5).trim());
      else if (line.startsWith('shallow ')) clientShallow.push(line.slice(8).trim());
      else if (line.startsWith('deepen ')) deepen = Number.parseInt(line.slice(7).trim(), 10);
    }
    const selection = computeFetch(wants, haves, clientShallow, deepen);
    sendRaw(res, 200, fetchSections(selection, haves, true), 'application/x-git-upload-pack-result');
    return;
  }

  if (firstLine.startsWith('want ')) {
    // Protocol v0: want lines up to a flush, then have lines and done.
    const sections = parseAllSections(body);
    if (sections === null) {
      sendJson(res, 400, { message: 'malformed pkt-line request' });
      return;
    }
    const wants: string[] = [];
    const haves: string[] = [];
    const clientShallow: string[] = [];
    let deepen: number | null = null;
    for (const line of dataLines(sections[0] ?? [])) {
      if (line.startsWith('want ')) wants.push(line.slice(5).trim().split(' ')[0]!);
      else if (line.startsWith('shallow ')) clientShallow.push(line.slice(8).trim());
      else if (line.startsWith('deepen ')) deepen = Number.parseInt(line.slice(7).trim(), 10);
    }
    for (const line of dataLines(sections[1] ?? [])) {
      if (line.startsWith('have ')) haves.push(line.slice(5).trim());
    }
    const selection = computeFetch(wants, haves, clientShallow, deepen);
    const parts: Buffer[] = [];
    for (const oid of selection.shallow) parts.push(pktLine(`shallow ${oid}\n`));
    for (const oid of selection.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
    const acked = haves.filter((have) => getObject(have) !== undefined);
    if (acked.length === 0) parts.push(pktLine('NAK\n'));
    else for (const have of acked) parts.push(pktLine(`ACK ${have}\n`));
    parts.push(...sidebandStream(writePack(selection.send)));
    parts.push(PKT_FLUSH);
    sendRaw(res, 200, Buffer.concat(parts), 'application/x-git-upload-pack-result');
    return;
  }

  sendJson(res, 400, { message: 'unsupported upload-pack request' });
}

interface PushCommand {
  oldOid: string;
  newOid: string;
  ref: string;
}

async function handleReceivePack(res: ServerResponse, repo: Repo, body: Buffer): Promise<void> {
  const first = parsePkts(body, 0);
  if (first === null) {
    sendJson(res, 400, { message: 'malformed pkt-line request' });
    return;
  }
  const commands: PushCommand[] = [];
  let capabilities = '';
  for (const packet of first.packets) {
    if (packet.kind !== 'data') continue;
    let line = packet.payload.toString('utf8').replace(/\n$/, '');
    const nul = line.indexOf('\0');
    if (nul >= 0) {
      capabilities = line.slice(nul + 1);
      line = line.slice(0, nul);
    }
    const parts = line.split(' ');
    if (parts.length === 3 && /^[0-9a-f]{40}$/.test(parts[0]!) && /^[0-9a-f]{40}$/.test(parts[1]!)) {
      commands.push({ oldOid: parts[0]!, newOid: parts[1]!, ref: parts[2]! });
    }
  }
  const pack = body.subarray(first.rest);
  let unpackError: string | null = null;
  if (pack.length > 0) {
    unpackError = await ingestPack(pack);
  }

  const reportLines: string[] = [unpackError === null ? 'unpack ok\n' : `unpack ${unpackError}\n`];
  for (const command of commands) {
    if (unpackError !== null) {
      reportLines.push(`ng ${command.ref} unpacker error\n`);
      continue;
    }
    const current = repo.refs.get(command.ref) ?? ZERO_OID;
    if (command.oldOid === ZERO_OID && current !== ZERO_OID) {
      reportLines.push(`ng ${command.ref} already exists\n`);
      continue;
    }
    if (command.oldOid !== current) {
      reportLines.push(`ng ${command.ref} stale info\n`);
      continue;
    }
    if (command.newOid === ZERO_OID) {
      repo.refs.delete(command.ref);
      reportLines.push(`ok ${command.ref}\n`);
      continue;
    }
    if (getObject(command.newOid) === undefined) {
      reportLines.push(`ng ${command.ref} missing object\n`);
      continue;
    }
    if (command.ref.startsWith('refs/heads/')) {
      if (peelToCommit(command.newOid) === null) {
        reportLines.push(`ng ${command.ref} invalid object\n`);
        continue;
      }
      if (current !== ZERO_OID && !isAncestor(current, command.newOid)) {
        reportLines.push(`ng ${command.ref} non-fast-forward\n`);
        continue;
      }
    }
    repo.refs.set(command.ref, command.newOid);
    reportLines.push(`ok ${command.ref}\n`);
  }

  const report = Buffer.concat([...reportLines.map((line) => pktLine(line)), PKT_FLUSH]);
  if (capabilities.split(' ').includes('side-band-64k')) {
    const parts: Buffer[] = [];
    const CHUNK = 65515;
    for (let offset = 0; offset < report.length; offset += CHUNK) {
      parts.push(sidebandPkt(1, report.subarray(offset, offset + CHUNK)));
    }
    parts.push(PKT_FLUSH);
    sendRaw(res, 200, Buffer.concat(parts), 'application/x-git-receive-pack-result');
  } else {
    sendRaw(res, 200, report, 'application/x-git-receive-pack-result');
  }
}

// ---------------------------------------------------------------------------
// REST v3

function repoJson(repo: Repo): Record<string, unknown> {
  const owner = repo.owner ?? VIEWER_LOGIN;
  return {
    id: repo.id,
    name: repo.name,
    full_name: `${owner}/${repo.name}`,
    private: repo.isPrivate,
    description: repo.description,
    default_branch: repo.defaultBranch,
    owner: { login: owner },
    html_url: `http://forge.invalid/${owner}/${repo.name}`,
  };
}

function issueJson(repo: Repo, issue: IssueRec): Record<string, unknown> {
  return {
    id: issue.id,
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((name) => ({ name, color: repo.labels.get(name)?.color ?? 'ededed' })),
    comments: issue.comments.length,
    user: { login: VIEWER_LOGIN },
  };
}

function pullJson(repo: Repo, pull: PullRec): Record<string, unknown> {
  const owner = repo.owner ?? VIEWER_LOGIN;
  return {
    id: pull.id,
    number: pull.number,
    title: pull.title,
    body: pull.body,
    state: pull.state,
    merged: pull.merged,
    merged_at: pull.mergedAt,
    merge_commit_sha: pull.mergeCommitSha,
    head: { ref: pull.head, sha: repo.refs.get(`refs/heads/${pull.head}`) ?? ZERO_OID, label: `${owner}:${pull.head}` },
    base: { ref: pull.base, sha: repo.refs.get(`refs/heads/${pull.base}`) ?? ZERO_OID, label: `${owner}:${pull.base}` },
    user: { login: VIEWER_LOGIN },
  };
}

/** Resolve a ref name (branch, tag, full ref or raw object id) to a commit oid. */
function resolveRef(repo: Repo, ref: string | undefined): string | null {
  if (ref === undefined || ref === '') {
    const tip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
    return tip === undefined ? null : peelToCommit(tip);
  }
  const candidates = [`refs/heads/${ref}`, `refs/tags/${ref}`, ref];
  for (const candidate of candidates) {
    const oid = repo.refs.get(candidate);
    if (oid !== undefined) return peelToCommit(oid);
  }
  if (/^[0-9a-f]{40}$/.test(ref) && getObject(ref) !== undefined) return peelToCommit(ref);
  return null;
}

/** Parse a JSON request body; answers 400 and returns null on malformed JSON. */
async function readJsonBody(req: IncomingMessage, res: ServerResponse): Promise<Record<string, unknown> | null> {
  const raw = await readBody(req);
  if (raw.length === 0) return {};
  try {
    const parsed: unknown = JSON.parse(raw.toString('utf8'));
    if (typeof parsed !== 'object' || parsed === null || Array.isArray(parsed)) return {};
    return parsed as Record<string, unknown>;
  } catch {
    sendJson(res, 400, { message: 'Malformed JSON in request body' });
    return null;
  }
}

function pageParams(url: URL): { perPage: number; page: number } {
  const perPage = Math.min(100, Math.max(1, Number.parseInt(url.searchParams.get('per_page') ?? '30', 10) || 30));
  const page = Math.max(1, Number.parseInt(url.searchParams.get('page') ?? '1', 10) || 1);
  return { perPage, page };
}

/** Slice a list for the page and set the Link header when a next page exists. */
function paginate<T>(req: IncomingMessage, res: ServerResponse, url: URL, items: T[]): T[] {
  const { perPage, page } = pageParams(url);
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  if (start + perPage < items.length) {
    const next = new URL(url.toString());
    next.searchParams.set('per_page', String(perPage));
    next.searchParams.set('page', String(page + 1));
    const host = req.headers.host ?? '127.0.0.1';
    res.setHeader('Link', `<http://${host}${next.pathname}${next.search}>; rel="next"`);
  }
  return slice;
}

function labelNamesOf(input: unknown): string[] {
  if (!Array.isArray(input)) return [];
  const names: string[] = [];
  for (const item of input) {
    if (typeof item === 'string') names.push(item);
    else if (typeof item === 'object' && item !== null && typeof (item as { name?: unknown }).name === 'string') {
      names.push((item as { name: string }).name);
    }
  }
  return names;
}

async function handleRest(req: IncomingMessage, res: ServerResponse, url: URL): Promise<void> {
  const method = req.method ?? 'GET';
  const path = url.pathname.replace(/\/+$/, '') || '/api/v3';
  const segments = path.split('/').filter((part) => part !== '');
  // segments[0] = 'api', segments[1] = 'v3'

  if (method === 'GET' && segments.length === 2) {
    sendJson(
      res,
      200,
      { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit' },
      { 'x-oauth-scopes': 'repo, read:org' },
    );
    return;
  }

  if (!bearerOk(req)) {
    sendJson(res, 401, { message: 'Bad credentials' });
    return;
  }

  if (method === 'GET' && path === '/api/v3/meta') {
    sendJson(res, 200, { installed_version: FORGE_VERSION });
    return;
  }
  if (method === 'GET' && path === '/api/v3/user') {
    sendJson(res, 200, { login: VIEWER_LOGIN, id: 1000, type: 'User' });
    return;
  }
  if (method === 'GET' && path === '/api/v3/rate_limit') {
    sendJson(res, 200, { rate: { limit: 5000, remaining: 5000, reset: 1893456000 }, resources: {} });
    return;
  }

  if (path === '/api/v3/user/repos') {
    if (method === 'POST') {
      const body = await readJsonBody(req, res);
      if (body === null) return;
      const name = typeof body.name === 'string' ? body.name : '';
      if (name === '' || /[\s/]/.test(name)) {
        sendJson(res, 422, { message: 'Repository creation failed: name is invalid' });
        return;
      }
      if (repos.has(name)) {
        sendJson(res, 422, { message: `Repository creation failed: name already exists on this account` });
        return;
      }
      const repo = createRepoRec(
        name,
        typeof body.description === 'string' ? body.description : '',
        typeof body.private === 'boolean' ? body.private : false,
      );
      repo.owner = VIEWER_LOGIN;
      sendJson(res, 201, repoJson(repo));
      return;
    }
    if (method === 'GET') {
      const all = [...repos.values()].filter((repo) => repo.owner === null || repo.owner === VIEWER_LOGIN);
      sendJson(res, 200, paginate(req, res, url, all).map(repoJson));
      return;
    }
  }

  if (segments[2] === 'repos' && segments.length >= 5) {
    const owner = decodeURIComponent(segments[3]!);
    const repo = findRepo(owner, decodeURIComponent(segments[4]!));
    if (repo === null) {
      notFound(res);
      return;
    }
    const rest = segments.slice(5).map((part) => decodeURIComponent(part));

    if (rest.length === 0) {
      if (method === 'GET') {
        sendJson(res, 200, repoJson(repo));
        return;
      }
      if (method === 'PATCH') {
        const body = await readJsonBody(req, res);
        if (body === null) return;
        if (typeof body.description === 'string') repo.description = body.description;
        if (typeof body.private === 'boolean') repo.isPrivate = body.private;
        if (typeof body.default_branch === 'string' && repo.refs.has(`refs/heads/${body.default_branch}`)) {
          repo.defaultBranch = body.default_branch;
        }
        sendJson(res, 200, repoJson(repo));
        return;
      }
      if (method === 'DELETE') {
        repos.delete(repo.name);
        sendJson(res, 204, undefined);
        return;
      }
    }

    if (rest[0] === 'contents') {
      await handleContents(req, res, url, repo, rest.slice(1).join('/'));
      return;
    }

    if (rest[0] === 'git' && rest[1] === 'refs') {
      if (method === 'POST' && rest.length === 2) {
        const body = await readJsonBody(req, res);
        if (body === null) return;
        const ref = typeof body.ref === 'string' ? body.ref : '';
        const sha = typeof body.sha === 'string' ? body.sha : '';
        if (!ref.startsWith('refs/') || getObject(sha) === undefined) {
          sendJson(res, 422, { message: 'Invalid ref or unknown object' });
          return;
        }
        if (repo.refs.has(ref)) {
          sendJson(res, 422, { message: 'Reference already exists' });
          return;
        }
        repo.refs.set(ref, sha);
        sendJson(res, 201, { ref, object: { sha, type: getObject(sha)!.type } });
        return;
      }
      if (method === 'GET') {
        const ref = `refs/${rest.slice(2).join('/')}`;
        const oid = repo.refs.get(ref);
        if (oid === undefined) {
          notFound(res);
          return;
        }
        sendJson(res, 200, { ref, object: { sha: oid, type: getObject(oid)?.type ?? 'commit' } });
        return;
      }
    }

    if (rest[0] === 'branches') {
      if (method === 'GET' && rest.length === 1) {
        const branches = [...repo.refs.entries()]
          .filter(([name]) => name.startsWith('refs/heads/'))
          .map(([name, oid]) => ({ name: name.slice('refs/heads/'.length), commit: { sha: oid }, protected: false }));
        sendJson(res, 200, branches);
        return;
      }
      if (method === 'GET' && rest.length >= 2) {
        const branch = rest.slice(1).join('/');
        const oid = repo.refs.get(`refs/heads/${branch}`);
        if (oid === undefined) {
          notFound(res);
          return;
        }
        sendJson(res, 200, { name: branch, commit: { sha: oid } });
        return;
      }
    }

    if (rest[0] === 'commits' && method === 'GET') {
      const tip = resolveRef(repo, url.searchParams.get('sha') ?? undefined);
      if (tip === null) {
        sendJson(res, 200, []);
        return;
      }
      const seen = new Set<string>();
      const ordered: string[] = [];
      const stack = [tip];
      while (stack.length > 0) {
        const oid = stack.pop()!;
        if (seen.has(oid)) continue;
        seen.add(oid);
        ordered.push(oid);
        const object = getObject(oid);
        if (object === undefined || object.type !== 'commit') continue;
        const parents = parseCommit(object.data).parents;
        for (let i = parents.length - 1; i >= 0; i--) stack.push(parents[i]!);
      }
      const items = ordered.map((oid) => {
        const commit = parseCommit(getObject(oid)!.data);
        return {
          sha: oid,
          commit: {
            message: commit.message.replace(/\n$/, ''),
            author: { name: VIEWER_LOGIN, email: `${VIEWER_LOGIN}@example.invalid` },
            committer: { name: VIEWER_LOGIN, email: `${VIEWER_LOGIN}@example.invalid` },
          },
          parents: commit.parents.map((parent) => ({ sha: parent })),
        };
      });
      sendJson(res, 200, paginate(req, res, url, items));
      return;
    }

    if (rest[0] === 'labels') {
      if (method === 'POST' && rest.length === 1) {
        const body = await readJsonBody(req, res);
        if (body === null) return;
        const name = typeof body.name === 'string' ? body.name : '';
        const color = typeof body.color === 'string' ? body.color.replace(/^#/, '') : 'ededed';
        if (name === '') {
          sendJson(res, 422, { message: 'Label name is required' });
          return;
        }
        if (repo.labels.has(name)) {
          sendJson(res, 422, { message: 'Label already exists' });
          return;
        }
        repo.labels.set(name, { name, color });
        sendJson(res, 201, { name, color });
        return;
      }
      if (method === 'GET' && rest.length === 1) {
        sendJson(res, 200, [...repo.labels.values()].map((label) => ({ name: label.name, color: label.color })));
        return;
      }
    }

    if (rest[0] === 'issues') {
      await handleIssues(req, res, url, repo, rest.slice(1));
      return;
    }

    if (rest[0] === 'pulls') {
      await handlePulls(req, res, url, repo, rest.slice(1));
      return;
    }
  }

  notFound(res);
}

/** The contents API: files and directories backed by the shared object store. */
async function handleContents(
  req: IncomingMessage,
  res: ServerResponse,
  url: URL,
  repo: Repo,
  filePath: string,
): Promise<void> {
  const method = req.method ?? 'GET';

  if (method === 'GET') {
    const commit = resolveRef(repo, url.searchParams.get('ref') ?? undefined);
    if (commit === null) {
      notFound(res);
      return;
    }
    const tree = parseCommit(getObject(commit)!.data).tree;
    if (filePath === '') {
      const entries = parseTree(getObject(tree)!.data).map((entry) => ({
        name: entry.name,
        path: entry.name,
        sha: entry.oid,
        type: entry.mode === '40000' ? 'dir' : 'file',
      }));
      sendJson(res, 200, entries);
      return;
    }
    // Walk to the target tree or blob.
    const segments = filePath.split('/');
    let currentTree = tree;
    for (let i = 0; i < segments.length; i++) {
      const entries = parseTree(getObject(currentTree)!.data);
      const entry = entries.find((candidate) => candidate.name === segments[i]);
      if (entry === undefined) {
        notFound(res);
        return;
      }
      if (i === segments.length - 1) {
        if (entry.mode === '40000') {
          const children = parseTree(getObject(entry.oid)!.data).map((child) => ({
            name: child.name,
            path: `${filePath}/${child.name}`,
            sha: child.oid,
            type: child.mode === '40000' ? 'dir' : 'file',
          }));
          sendJson(res, 200, children);
          return;
        }
        const blob = getObject(entry.oid)!;
        const base64 = blob.data.toString('base64').replace(/.{60}/g, '$&\n');
        sendJson(res, 200, {
          type: 'file',
          name: entry.name,
          path: filePath,
          sha: entry.oid,
          size: blob.data.length,
          encoding: 'base64',
          content: base64.endsWith('\n') ? base64 : `${base64}\n`,
        });
        return;
      }
      if (entry.mode !== '40000') {
        notFound(res);
        return;
      }
      currentTree = entry.oid;
    }
    notFound(res);
    return;
  }

  if (method === 'PUT' || method === 'DELETE') {
    const body = await readJsonBody(req, res);
    if (body === null) return;
    const message = typeof body.message === 'string' ? body.message : '';
    const branch = typeof body.branch === 'string' && body.branch !== '' ? body.branch : repo.defaultBranch;
    const refName = `refs/heads/${branch}`;
    const tip = repo.refs.get(refName);
    const flat = tip === undefined ? new Map<string, TreeEntry>() : commitFiles(tip);
    const existing = flat.get(filePath);

    if (method === 'PUT') {
      if (typeof body.content !== 'string') {
        sendJson(res, 422, { message: 'content is required' });
        return;
      }
      const shaGiven = typeof body.sha === 'string' ? body.sha : undefined;
      if (existing !== undefined && shaGiven !== existing.oid) {
        sendJson(res, 409, { message: 'SHA mismatch: the file changed since it was read' });
        return;
      }
      if (existing === undefined && shaGiven !== undefined) {
        sendJson(res, 409, { message: 'SHA supplied for a file that does not exist' });
        return;
      }
      const data = Buffer.from(body.content.replace(/\s+/g, ''), 'base64');
      const blobOid = storeObject('blob', data);
      flat.set(filePath, { mode: existing?.mode ?? '100644', name: filePath.split('/').pop()!, oid: blobOid });
      const tree = buildTreeFromFlat(flat);
      const commitOid = storeObject('commit', buildCommitData(tree, tip === undefined ? [] : [tip], message === '' ? `Update ${filePath}` : message));
      repo.refs.set(refName, commitOid);
      sendJson(res, existing === undefined ? 201 : 200, {
        content: { name: filePath.split('/').pop()!, path: filePath, sha: blobOid, size: data.length, encoding: 'base64', type: 'file' },
        commit: { sha: commitOid },
      });
      return;
    }

    // DELETE
    if (existing === undefined) {
      notFound(res);
      return;
    }
    const shaGiven = typeof body.sha === 'string' ? body.sha : undefined;
    if (shaGiven !== existing.oid) {
      sendJson(res, 409, { message: 'SHA mismatch: the file changed since it was read' });
      return;
    }
    flat.delete(filePath);
    const tree = buildTreeFromFlat(flat);
    const commitOid = storeObject('commit', buildCommitData(tree, tip === undefined ? [] : [tip], message === '' ? `Delete ${filePath}` : message));
    repo.refs.set(refName, commitOid);
    sendJson(res, 200, { content: null, commit: { sha: commitOid } });
    return;
  }

  notFound(res);
}

async function handleIssues(
  req: IncomingMessage,
  res: ServerResponse,
  url: URL,
  repo: Repo,
  rest: string[],
): Promise<void> {
  const method = req.method ?? 'GET';

  if (rest.length === 0) {
    if (method === 'POST') {
      const body = await readJsonBody(req, res);
      if (body === null) return;
      const title = typeof body.title === 'string' ? body.title : '';
      if (title === '') {
        sendJson(res, 422, { message: 'Title is required' });
        return;
      }
      const labels = labelNamesOf(body.labels);
      for (const label of labels) {
        if (!repo.labels.has(label)) {
          sendJson(res, 422, { message: `Unknown label: ${label}` });
          return;
        }
      }
      const issue: IssueRec = {
        id: issueIdCounter++,
        number: repo.nextNumber++,
        title,
        body: typeof body.body === 'string' ? body.body : '',
        state: 'open',
        labels,
        comments: [],
      };
      repo.issues.set(issue.number, issue);
      sendJson(res, 201, issueJson(repo, issue));
      return;
    }
    if (method === 'GET') {
      const state = url.searchParams.get('state') ?? 'open';
      let items = [...repo.issues.values()].filter((issue) => state === 'all' || issue.state === state);
      const direction = url.searchParams.get('direction') ?? 'asc';
      items = items.sort((a, b) => (direction === 'desc' ? b.number - a.number : a.number - b.number));
      sendJson(res, 200, paginate(req, res, url, items).map((issue) => issueJson(repo, issue)));
      return;
    }
  }

  const number = Number.parseInt(rest[0] ?? '', 10);
  const issue = Number.isNaN(number) ? undefined : repo.issues.get(number);
  if (issue === undefined) {
    notFound(res);
    return;
  }

  if (rest.length === 1) {
    if (method === 'GET') {
      sendJson(res, 200, issueJson(repo, issue));
      return;
    }
    if (method === 'PATCH') {
      const body = await readJsonBody(req, res);
      if (body === null) return;
      if (typeof body.title === 'string') issue.title = body.title;
      if (typeof body.body === 'string') issue.body = body.body;
      if (body.state === 'open' || body.state === 'closed') issue.state = body.state;
      if (body.labels !== undefined) {
        const labels = labelNamesOf(body.labels);
        for (const label of labels) {
          if (!repo.labels.has(label)) {
            sendJson(res, 422, { message: `Unknown label: ${label}` });
            return;
          }
        }
        issue.labels = labels;
      }
      sendJson(res, 200, issueJson(repo, issue));
      return;
    }
  }

  if (rest.length === 2 && rest[1] === 'comments') {
    if (method === 'POST') {
      const body = await readJsonBody(req, res);
      if (body === null) return;
      const comment = { id: commentIdCounter++, body: typeof body.body === 'string' ? body.body : '' };
      issue.comments.push(comment);
      sendJson(res, 201, { id: comment.id, body: comment.body, user: { login: VIEWER_LOGIN } });
      return;
    }
    if (method === 'GET') {
      sendJson(res, 200, issue.comments.map((comment) => ({ id: comment.id, body: comment.body, user: { login: VIEWER_LOGIN } })));
      return;
    }
  }

  notFound(res);
}

/** Line-multiset diff counts between two blob texts (additions >= 1 when bytes differ). */
function lineDiffCounts(baseText: string, headText: string): { additions: number; deletions: number } {
  const countLines = (text: string): Map<string, number> => {
    const counts = new Map<string, number>();
    if (text === '') return counts;
    for (const line of text.split('\n')) counts.set(line, (counts.get(line) ?? 0) + 1);
    return counts;
  };
  const baseCounts = countLines(baseText);
  const headCounts = countLines(headText);
  let additions = 0;
  let deletions = 0;
  for (const [line, count] of headCounts) additions += Math.max(0, count - (baseCounts.get(line) ?? 0));
  for (const [line, count] of baseCounts) deletions += Math.max(0, count - (headCounts.get(line) ?? 0));
  if (additions === 0 && deletions === 0 && baseText !== headText) {
    additions = 1;
    deletions = 1;
  }
  return { additions, deletions };
}

interface MergeOutcome {
  tree: string;
}

/** The per-path three-way merge of head into base against their merge base; null on conflict. */
function tryMerge(repo: Repo, baseBranch: string, headBranch: string): MergeOutcome | null {
  const baseTip = repo.refs.get(`refs/heads/${baseBranch}`);
  const headTip = repo.refs.get(`refs/heads/${headBranch}`);
  if (baseTip === undefined || headTip === undefined) return null;
  const baseCommit = peelToCommit(baseTip);
  const headCommit = peelToCommit(headTip);
  if (baseCommit === null || headCommit === null) return null;
  const ancestor = mergeBase(baseCommit, headCommit);
  const ancestorFiles = ancestor === null ? new Map<string, TreeEntry>() : commitFiles(ancestor);
  const baseFiles = commitFiles(baseCommit);
  const headFiles = commitFiles(headCommit);
  const merged = new Map<string, TreeEntry>();
  const paths = new Set([...ancestorFiles.keys(), ...baseFiles.keys(), ...headFiles.keys()]);
  const same = (a: TreeEntry | undefined, b: TreeEntry | undefined): boolean =>
    a === undefined && b === undefined ? true : a !== undefined && b !== undefined && a.oid === b.oid && a.mode === b.mode;
  for (const path of paths) {
    const a = ancestorFiles.get(path);
    const b = baseFiles.get(path);
    const h = headFiles.get(path);
    let winner: TreeEntry | undefined;
    if (same(h, b)) winner = b;
    else if (same(b, a)) winner = h;
    else if (same(h, a)) winner = b;
    else return null;
    if (winner !== undefined) merged.set(path, winner);
  }
  return { tree: buildTreeFromFlat(merged) };
}

/** Squash-merge head into base: one commit on the base tip carrying the merged tree. */
function squashMerge(repo: Repo, pull: PullRec): string | null {
  const outcome = tryMerge(repo, pull.base, pull.head);
  if (outcome === null) return null;
  const baseTip = repo.refs.get(`refs/heads/${pull.base}`)!;
  const baseCommit = peelToCommit(baseTip)!;
  const message = pull.body === '' ? pull.title : `${pull.title}\n\n${pull.body}`;
  const commitOid = storeObject('commit', buildCommitData(outcome.tree, [baseCommit], message));
  repo.refs.set(`refs/heads/${pull.base}`, commitOid);
  return commitOid;
}

async function handlePulls(
  req: IncomingMessage,
  res: ServerResponse,
  url: URL,
  repo: Repo,
  rest: string[],
): Promise<void> {
  const method = req.method ?? 'GET';

  if (rest.length === 0) {
    if (method === 'POST') {
      const body = await readJsonBody(req, res);
      if (body === null) return;
      const title = typeof body.title === 'string' ? body.title : '';
      const head = typeof body.head === 'string' ? body.head : '';
      const base = typeof body.base === 'string' ? body.base : '';
      if (title === '' || head === '' || base === '') {
        sendJson(res, 422, { message: 'title, head and base are required' });
        return;
      }
      if (repo.refs.get(`refs/heads/${head}`) === undefined || repo.refs.get(`refs/heads/${base}`) === undefined) {
        sendJson(res, 422, { message: 'Head or base branch does not exist' });
        return;
      }
      const pull: PullRec = {
        id: issueIdCounter++,
        number: repo.nextNumber++,
        title,
        body: typeof body.body === 'string' ? body.body : '',
        state: 'open',
        head,
        base,
        merged: false,
        mergedAt: null,
        mergeCommitSha: null,
      };
      repo.pulls.set(pull.number, pull);
      sendJson(res, 201, pullJson(repo, pull));
      return;
    }
    if (method === 'GET') {
      const state = url.searchParams.get('state') ?? 'open';
      const items = [...repo.pulls.values()].filter((pull) => {
        if (state === 'all') return true;
        if (state === 'closed') return pull.state === 'closed';
        return pull.state === 'open';
      });
      sendJson(res, 200, paginate(req, res, url, items).map((pull) => pullJson(repo, pull)));
      return;
    }
  }

  const number = Number.parseInt(rest[0] ?? '', 10);
  const pull = Number.isNaN(number) ? undefined : repo.pulls.get(number);
  if (pull === undefined) {
    notFound(res);
    return;
  }

  if (rest.length === 1) {
    if (method === 'GET') {
      sendJson(res, 200, pullJson(repo, pull));
      return;
    }
    if (method === 'PATCH') {
      const body = await readJsonBody(req, res);
      if (body === null) return;
      if (typeof body.title === 'string') pull.title = body.title;
      if (typeof body.body === 'string') pull.body = body.body;
      if (body.state === 'open' || body.state === 'closed') pull.state = body.state;
      sendJson(res, 200, pullJson(repo, pull));
      return;
    }
  }

  if (rest.length === 2 && rest[1] === 'files' && method === 'GET') {
    const baseTip = repo.refs.get(`refs/heads/${pull.base}`);
    const headTip = repo.refs.get(`refs/heads/${pull.head}`);
    if (baseTip === undefined || headTip === undefined) {
      sendJson(res, 200, []);
      return;
    }
    const baseFiles = commitFiles(peelToCommit(baseTip)!);
    const headFiles = commitFiles(peelToCommit(headTip)!);
    const paths = new Set([...baseFiles.keys(), ...headFiles.keys()]);
    const files: Array<Record<string, unknown>> = [];
    for (const path of [...paths].sort()) {
      const b = baseFiles.get(path);
      const h = headFiles.get(path);
      if (b !== undefined && h !== undefined && b.oid === h.oid) continue;
      const baseText = b === undefined ? '' : (getObject(b.oid)?.data.toString('utf8') ?? '');
      const headText = h === undefined ? '' : (getObject(h.oid)?.data.toString('utf8') ?? '');
      const { additions, deletions } = lineDiffCounts(baseText, headText);
      files.push({
        filename: path,
        status: b === undefined ? 'added' : h === undefined ? 'removed' : 'modified',
        additions,
        deletions,
        changes: additions + deletions,
        sha: h?.oid ?? b!.oid,
      });
    }
    sendJson(res, 200, files);
    return;
  }

  if (rest.length === 2 && rest[1] === 'merge' && method === 'PUT') {
    await readJsonBody(req, res); // the merge_method body; squash, merge and rebase all land as one commit here
    if (pull.merged) {
      sendJson(res, 405, { message: 'Pull Request has already been merged' });
      return;
    }
    if (pull.state !== 'open') {
      sendJson(res, 405, { message: 'Pull Request is not open' });
      return;
    }
    const sha = squashMerge(repo, pull);
    if (sha === null) {
      sendJson(res, 405, { message: 'Pull Request is not mergeable: conflicts must be resolved first' });
      return;
    }
    pull.merged = true;
    pull.state = 'closed';
    pull.mergedAt = new Date().toISOString();
    pull.mergeCommitSha = sha;
    sendJson(res, 200, { sha, merged: true, message: 'Pull Request successfully merged' });
    return;
  }

  notFound(res);
}

// ---------------------------------------------------------------------------
// GraphQL v4: a small parser and executor over the same store.

type GqlValue =
  | { kind: 'variable'; name: string }
  | { kind: 'string'; value: string }
  | { kind: 'int'; value: number }
  | { kind: 'float'; value: number }
  | { kind: 'boolean'; value: boolean }
  | { kind: 'null' }
  | { kind: 'enum'; value: string }
  | { kind: 'list'; values: GqlValue[] }
  | { kind: 'object'; fields: Array<{ name: string; value: GqlValue }> };

interface GqlField {
  name: string;
  alias: string | null;
  args: Array<{ name: string; value: GqlValue }>;
  selection: GqlSelection[] | null;
}

type GqlSelection =
  | { kind: 'field'; field: GqlField }
  | { kind: 'inline'; typeCondition: string | null; selection: GqlSelection[] }
  | { kind: 'spread'; name: string };

interface GqlOperation {
  type: 'query' | 'mutation';
  name: string | null;
  selection: GqlSelection[];
}

interface GqlDocument {
  operations: GqlOperation[];
  fragments: Map<string, GqlSelection[]>;
}

function tokenizeGraphql(source: string): string[] {
  const tokens: string[] = [];
  let i = 0;
  while (i < source.length) {
    const ch = source[i]!;
    if (ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r' || ch === ',' || ch === '﻿') {
      i++;
      continue;
    }
    if (ch === '#') {
      while (i < source.length && source[i] !== '\n') i++;
      continue;
    }
    if (source.startsWith('...', i)) {
      tokens.push('...');
      i += 3;
      continue;
    }
    if ('{}()[]:=@$|!&'.includes(ch)) {
      tokens.push(ch);
      i++;
      continue;
    }
    if (ch === '"') {
      if (source.startsWith('"""', i)) {
        const end = source.indexOf('"""', i + 3);
        if (end === -1) throw new Error('unterminated block string');
        tokens.push(`"${source.slice(i + 3, end)}"`);
        i = end + 3;
        continue;
      }
      let j = i + 1;
      let value = '';
      while (j < source.length && source[j] !== '"') {
        if (source[j] === '\\') {
          const esc = source[j + 1]!;
          value += esc === 'n' ? '\n' : esc === 't' ? '\t' : esc === 'r' ? '\r' : esc === 'b' ? '\b' : esc === 'f' ? '\f' : esc === '/' ? '/' : esc === '\\' ? '\\' : esc === '"' ? '"' : esc === 'u' ? String.fromCharCode(parseInt(source.slice(j + 2, j + 6), 16)) : esc;
          j += esc === 'u' ? 6 : 2;
        } else {
          value += source[j];
          j++;
        }
      }
      if (j >= source.length) throw new Error('unterminated string');
      tokens.push(`"${value}"`);
      i = j + 1;
      continue;
    }
    if (/[0-9-]/.test(ch)) {
      let j = i;
      while (j < source.length && /[0-9.eE+-]/.test(source[j]!)) j++;
      tokens.push(source.slice(i, j));
      i = j;
      continue;
    }
    if (/[_A-Za-z]/.test(ch)) {
      let j = i;
      while (j < source.length && /[_0-9A-Za-z]/.test(source[j]!)) j++;
      tokens.push(source.slice(i, j));
      i = j;
      continue;
    }
    throw new Error(`unexpected character ${JSON.stringify(ch)} in GraphQL document`);
  }
  return tokens;
}

function parseGraphql(source: string): GqlDocument {
  const tokens = tokenizeGraphql(source);
  let pos = 0;
  const peek = (): string | undefined => tokens[pos];
  const next = (): string => {
    const token = tokens[pos++];
    if (token === undefined) throw new Error('unexpected end of GraphQL document');
    return token;
  };
  const expect = (token: string): void => {
    const got = next();
    if (got !== token) throw new Error(`expected ${token}, found ${got}`);
  };

  const parseValue = (): GqlValue => {
    const token = next();
    if (token === '$') {
      // The tokenizer keeps '$' separate from the name in this grammar position.
      return { kind: 'variable', name: next() };
    }
    if (token.startsWith('$')) return { kind: 'variable', name: token.slice(1) };
    if (token.startsWith('"')) return { kind: 'string', value: token.slice(1, -1) };
    if (token === '[') {
      const values: GqlValue[] = [];
      while (peek() !== ']') values.push(parseValue());
      expect(']');
      return { kind: 'list', values };
    }
    if (token === '{') {
      const fields: Array<{ name: string; value: GqlValue }> = [];
      while (peek() !== '}') {
        const name = next();
        expect(':');
        fields.push({ name, value: parseValue() });
      }
      expect('}');
      return { kind: 'object', fields };
    }
    if (token === 'true' || token === 'false') return { kind: 'boolean', value: token === 'true' };
    if (token === 'null') return { kind: 'null' };
    if (/^-?\d+$/.test(token)) return { kind: 'int', value: Number.parseInt(token, 10) };
    if (/^-?\d+(\.\d+)?([eE][+-]?\d+)?$/.test(token)) return { kind: 'float', value: Number.parseFloat(token) };
    return { kind: 'enum', value: token };
  };

  const parseSelectionSet = (): GqlSelection[] => {
    expect('{');
    const selections: GqlSelection[] = [];
    while (peek() !== '}') {
      if (peek() === '...') {
        next();
        const name = next();
        if (name === 'on') {
          const typeCondition = next();
          selections.push({ kind: 'inline', typeCondition, selection: parseSelectionSet() });
        } else {
          selections.push({ kind: 'spread', name });
        }
        continue;
      }
      let name = next();
      let alias: string | null = null;
      if (peek() === ':') {
        next();
        alias = name;
        name = next();
      }
      const args: Array<{ name: string; value: GqlValue }> = [];
      if (peek() === '(') {
        next();
        while (peek() !== ')') {
          const argName = next();
          expect(':');
          args.push({ name: argName, value: parseValue() });
        }
        expect(')');
      }
      // Directives are not used by the suite; skip any that appear.
      while (peek() === '@') {
        next();
        next();
        if (peek() === '(') {
          let depth = 0;
          do {
            const token = next();
            if (token === '(') depth++;
            else if (token === ')') depth--;
          } while (depth > 0);
        }
      }
      const selection = peek() === '{' ? parseSelectionSet() : null;
      selections.push({ kind: 'field', field: { name, alias, args, selection } });
    }
    expect('}');
    return selections;
  };

  const skipBalanced = (open: string, close: string): void => {
    expect(open);
    let depth = 1;
    while (depth > 0) {
      const token = next();
      if (token === open) depth++;
      else if (token === close) depth--;
    }
  };

  const operations: GqlOperation[] = [];
  const fragments = new Map<string, GqlSelection[]>();
  while (pos < tokens.length) {
    const token = peek()!;
    if (token === '{') {
      operations.push({ type: 'query', name: null, selection: parseSelectionSet() });
      continue;
    }
    if (token === 'query' || token === 'mutation' || token === 'subscription') {
      next();
      let name: string | null = null;
      if (peek() !== '(' && peek() !== '{' && peek() !== '@') name = next();
      if (peek() === '(') skipBalanced('(', ')');
      while (peek() === '@') {
        next();
        next();
        if (peek() === '(') skipBalanced('(', ')');
      }
      operations.push({ type: token === 'mutation' ? 'mutation' : 'query', name, selection: parseSelectionSet() });
      continue;
    }
    if (token === 'fragment') {
      next();
      const name = next();
      expect('on');
      next(); // type condition
      fragments.set(name, parseSelectionSet());
      continue;
    }
    throw new Error(`unexpected token ${token} in GraphQL document`);
  }
  return { operations, fragments };
}

/** Resolve an AST value against the operation's variables into plain JSON data. */
function valueOf(value: GqlValue, variables: Record<string, unknown>): unknown {
  switch (value.kind) {
    case 'variable':
      return variables[value.name];
    case 'string':
    case 'enum':
      return value.value;
    case 'int':
    case 'float':
    case 'boolean':
      return value.value;
    case 'null':
      return null;
    case 'list':
      return value.values.map((item) => valueOf(item, variables));
    case 'object': {
      const out: Record<string, unknown> = {};
      for (const field of value.fields) out[field.name] = valueOf(field.value, variables);
      return out;
    }
  }
}

// ---------------------------------------------------------------------------
// GraphQL executor

function globalId(raw: string): string {
  return Buffer.from(raw, 'utf8').toString('base64url');
}

function decodeGlobalId(id: string): string | null {
  try {
    return Buffer.from(id, 'base64url').toString('utf8');
  } catch {
    return null;
  }
}

function repoGlobalId(repo: Repo): string {
  return globalId(`Repository:${repo.id}`);
}

function issueGlobalId(repo: Repo, issue: IssueRec): string {
  return globalId(`Issue:${repo.id}:${issue.number}`);
}

function pullGlobalId(repo: Repo, pull: PullRec): string {
  return globalId(`PullRequest:${repo.id}:${pull.number}`);
}

function repoById(id: number): Repo | null {
  for (const repo of repos.values()) if (repo.id === id) return repo;
  return null;
}

type GqlObj = { __typename: string; [key: string]: unknown };

function repoObj(repo: Repo): GqlObj {
  return { __typename: 'Repository', repo };
}

function issueObj(repo: Repo, issue: IssueRec): GqlObj {
  return { __typename: 'Issue', repo, issue };
}

function pullObj(repo: Repo, pull: PullRec): GqlObj {
  return { __typename: 'PullRequest', repo, pull };
}

const GQL_TYPE_REGISTRY: Record<string, { kind: 'OBJECT' | 'ENUM'; fields?: string[]; enumValues?: string[] }> = {
  Query: { kind: 'OBJECT', fields: ['viewer', 'repository', 'node', 'search', '__type', '__schema'] },
  Mutation: {
    kind: 'OBJECT',
    fields: ['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment'],
  },
  User: { kind: 'OBJECT', fields: ['id', 'login', 'name', 'email', 'url'] },
  Organization: { kind: 'OBJECT', fields: ['id', 'login', 'name', 'url'] },
  Repository: {
    kind: 'OBJECT',
    fields: [
      'id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'description', 'isPrivate',
      'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'hasWikiEnabled',
      'issue', 'issues', 'pullRequest', 'pullRequests', 'url', 'createdAt', 'updatedAt',
    ],
  },
  Issue: {
    kind: 'OBJECT',
    fields: ['id', 'number', 'title', 'state', 'body', 'author', 'repository', 'labels', 'comments', 'createdAt', 'updatedAt', 'url', 'closed'],
  },
  PullRequest: {
    kind: 'OBJECT',
    fields: [
      'id', 'number', 'title', 'state', 'body', 'merged', 'mergeable', 'headRefName', 'baseRefName',
      'headRef', 'baseRef', 'files', 'author', 'repository', 'mergeCommit', 'createdAt', 'updatedAt', 'url',
    ],
  },
  Ref: { kind: 'OBJECT', fields: ['id', 'name', 'prefix', 'target'] },
  IssueConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'totalCount'] },
  IssueEdge: { kind: 'OBJECT', fields: ['node', 'cursor'] },
  PullRequestConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'totalCount'] },
  PullRequestEdge: { kind: 'OBJECT', fields: ['node', 'cursor'] },
  PullRequestChangedFileConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'totalCount'] },
  PullRequestChangedFileEdge: { kind: 'OBJECT', fields: ['node', 'cursor'] },
  PullRequestChangedFile: { kind: 'OBJECT', fields: ['path', 'additions', 'deletions', 'changeType'] },
  PageInfo: { kind: 'OBJECT', fields: ['hasNextPage', 'hasPreviousPage', 'startCursor', 'endCursor'] },
  IssueComment: { kind: 'OBJECT', fields: ['id', 'body', 'author', 'createdAt'] },
  IssueCommentEdge: { kind: 'OBJECT', fields: ['node', 'cursor'] },
  CreateIssuePayload: { kind: 'OBJECT', fields: ['issue', 'clientMutationId'] },
  CloseIssuePayload: { kind: 'OBJECT', fields: ['issue', 'clientMutationId'] },
  CreatePullRequestPayload: { kind: 'OBJECT', fields: ['pullRequest', 'clientMutationId'] },
  MergePullRequestPayload: { kind: 'OBJECT', fields: ['pullRequest', 'clientMutationId'] },
  AddCommentPayload: { kind: 'OBJECT', fields: ['commentEdge', 'subject', 'clientMutationId'] },
  __Type: { kind: 'OBJECT', fields: ['name', 'kind', 'description', 'fields', 'enumValues', 'possibleTypes', 'ofType'] },
  __Field: { kind: 'OBJECT', fields: ['name', 'description', 'args', 'type'] },
  __EnumValue: { kind: 'OBJECT', fields: ['name', 'description'] },
  IssueState: { kind: 'ENUM', enumValues: ['OPEN', 'CLOSED'] },
  PullRequestState: { kind: 'ENUM', enumValues: ['OPEN', 'CLOSED', 'MERGED'] },
  MergeableState: { kind: 'ENUM', enumValues: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'] },
  SearchType: { kind: 'ENUM', enumValues: ['ISSUE', 'REPOSITORY', 'USER'] },
  OrderDirection: { kind: 'ENUM', enumValues: ['ASC', 'DESC'] },
  IssueOrderField: { kind: 'ENUM', enumValues: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'] },
  PullRequestOrderField: { kind: 'ENUM', enumValues: ['CREATED_AT', 'UPDATED_AT'] },
  PullRequestMergeMethod: { kind: 'ENUM', enumValues: ['MERGE', 'SQUASH', 'REBASE'] },
};

class GqlFieldError extends Error {}

interface GqlContext {
  variables: Record<string, unknown>;
  fragments: Map<string, GqlSelection[]>;
  errors: Array<{ message: string }>;
}

function argsOf(field: GqlField, ctx: GqlContext): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const arg of field.args) out[arg.name] = valueOf(arg.value, ctx.variables);
  return out;
}

function cursorOf(index: number): string {
  return globalId(`cursor:${index}`);
}

function indexOfCursor(cursor: string): number {
  const raw = decodeGlobalId(cursor);
  const match = raw === null ? null : /^cursor:(\d+)$/.exec(raw);
  return match === null ? -1 : Number.parseInt(match[1]!, 10);
}

interface ConnectionResult {
  items: GqlObj[];
  total: number;
  startIndex: number;
}

/** Slice a full, ordered item list into a connection page. */
function connectionPage(items: GqlObj[], args: Record<string, unknown>): ConnectionResult {
  let start = 0;
  if (typeof args.after === 'string') start = indexOfCursor(args.after) + 1;
  const first = typeof args.first === 'number' ? Math.max(0, args.first) : 100;
  return { items: items.slice(start, start + first), total: items.length, startIndex: start };
}

function connectionObj(typename: string, edgeTypename: string, page: ConnectionResult): GqlObj {
  const hasNextPage = page.startIndex + page.items.length < page.total;
  return {
    __typename: typename,
    edgeTypename,
    nodesRaw: page.items,
    cursors: page.items.map((_, i) => cursorOf(page.startIndex + i)),
    pageInfo: {
      __typename: 'PageInfo',
      hasNextPage,
      hasPreviousPage: page.startIndex > 0,
      startCursor: page.items.length > 0 ? cursorOf(page.startIndex) : null,
      endCursor: page.items.length > 0 ? cursorOf(page.startIndex + page.items.length - 1) : null,
    } satisfies GqlObj,
    totalCount: page.total,
  };
}

/** The changed-file list of a pull request (paths plus line counts), shared by REST and GraphQL shapes. */
function pullFilesList(repo: Repo, pull: PullRec): Array<{ path: string; additions: number; deletions: number; status: string }> {
  const baseTip = repo.refs.get(`refs/heads/${pull.base}`);
  const headTip = repo.refs.get(`refs/heads/${pull.head}`);
  if (baseTip === undefined || headTip === undefined) return [];
  const baseFiles = commitFiles(peelToCommit(baseTip)!);
  const headFiles = commitFiles(peelToCommit(headTip)!);
  const paths = new Set([...baseFiles.keys(), ...headFiles.keys()]);
  const out: Array<{ path: string; additions: number; deletions: number; status: string }> = [];
  for (const path of [...paths].sort()) {
    const b = baseFiles.get(path);
    const h = headFiles.get(path);
    if (b !== undefined && h !== undefined && b.oid === h.oid) continue;
    const baseText = b === undefined ? '' : (getObject(b.oid)?.data.toString('utf8') ?? '');
    const headText = h === undefined ? '' : (getObject(h.oid)?.data.toString('utf8') ?? '');
    const { additions, deletions } = lineDiffCounts(baseText, headText);
    out.push({ path, additions, deletions, status: b === undefined ? 'added' : h === undefined ? 'removed' : 'modified' });
  }
  return out;
}

function pullStateGql(pull: PullRec): string {
  if (pull.merged) return 'MERGED';
  return pull.state === 'open' ? 'OPEN' : 'CLOSED';
}

/** Resolve one field on one object; throws GqlFieldError for unknown fields. */
function gqlField(obj: GqlObj, field: GqlField, ctx: GqlContext): unknown {
  const name = field.name;
  const args = argsOf(field, ctx);
  const fail = (): never => {
    throw new GqlFieldError(`Field '${name}' doesn't exist on type '${obj.__typename}'`);
  };

  switch (obj.__typename) {
    case 'Query': {
      if (name === 'viewer') return { __typename: 'User', login: VIEWER_LOGIN } satisfies GqlObj;
      if (name === 'repository') {
        const owner = typeof args.owner === 'string' ? args.owner : '';
        const repoName = typeof args.name === 'string' ? args.name : '';
        const repo = findRepo(owner, repoName);
        return repo === null ? null : repoObj(repo);
      }
      if (name === 'node') {
        return typeof args.id === 'string' ? nodeByGlobalId(args.id) : null;
      }
      if (name === '__type') {
        const typeName = typeof args.name === 'string' ? args.name : '';
        const def = GQL_TYPE_REGISTRY[typeName];
        if (def === undefined) return null;
        return {
          __typename: '__Type',
          name: typeName,
          kind: def.kind === 'ENUM' ? 'ENUM' : 'OBJECT',
          fields: def.fields === undefined ? null : def.fields.map((fieldName) => ({ __typename: '__Field', name: fieldName })),
          enumValues: def.enumValues === undefined ? null : def.enumValues.map((value) => ({ __typename: '__EnumValue', name: value })),
        } satisfies GqlObj;
      }
      if (name === '__schema') return { __typename: '__Schema' };
      return fail();
    }
    case '__Schema': {
      if (name === 'queryType') return { __typename: '__Type', name: 'Query', kind: 'OBJECT', fields: [], enumValues: null };
      if (name === 'mutationType') return { __typename: '__Type', name: 'Mutation', kind: 'OBJECT', fields: [], enumValues: null };
      return fail();
    }
    case '__Type': {
      if (name === 'name' || name === 'kind') return obj[name];
      if (name === 'fields') return obj.fields ?? null;
      if (name === 'enumValues') return obj.enumValues ?? null;
      if (name === 'description') return null;
      if (name === 'possibleTypes') return null;
      if (name === 'ofType') return null;
      return fail();
    }
    case '__Field': {
      if (name === 'name') return obj.name;
      if (name === 'description') return null;
      if (name === 'args') return [];
      if (name === 'type') return null;
      return fail();
    }
    case '__EnumValue': {
      if (name === 'name') return obj.name;
      if (name === 'description') return null;
      return fail();
    }
    case 'User':
    case 'Organization': {
      if (name === 'login') return obj.login;
      if (name === 'id') return globalId(`User:1000`);
      if (name === 'name') return obj.login === VIEWER_LOGIN ? 'ada iversen' : obj.login;
      if (name === 'email') return `${String(obj.login)}@example.invalid`;
      if (name === 'url') return `http://forge.invalid/${String(obj.login)}`;
      return fail();
    }
    case 'Repository': {
      const repo = obj.repo as Repo;
      switch (name) {
        case 'id':
          return repoGlobalId(repo);
        case 'databaseId':
          return repo.id;
        case 'name':
          return repo.name;
        case 'nameWithOwner':
          return `${repo.owner ?? VIEWER_LOGIN}/${repo.name}`;
        case 'owner':
          return { __typename: 'User', login: repo.owner ?? VIEWER_LOGIN } satisfies GqlObj;
        case 'description':
          return repo.description;
        case 'isPrivate':
          return repo.isPrivate;
        case 'defaultBranchRef': {
          const tip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
          if (tip === undefined) return null;
          return { __typename: 'Ref', repo, name: repo.defaultBranch, oid: tip } satisfies GqlObj;
        }
        case 'viewerPermission':
          return 'ADMIN';
        case 'hasIssuesEnabled':
          return true;
        case 'hasWikiEnabled':
          return false;
        case 'url':
          return `http://forge.invalid/${repo.owner ?? VIEWER_LOGIN}/${repo.name}`;
        case 'issue': {
          const number = typeof args.number === 'number' ? args.number : -1;
          const issue = repo.issues.get(number);
          return issue === undefined ? null : issueObj(repo, issue);
        }
        case 'issues': {
          let issues = [...repo.issues.values()];
          const states = Array.isArray(args.states) ? (args.states as string[]) : null;
          if (states !== null) issues = issues.filter((issue) => states.includes(issue.state.toUpperCase()));
          let direction = 'ASC';
          const orderBy = args.orderBy as { field?: string; direction?: string } | undefined;
          if (orderBy !== undefined && typeof orderBy.direction === 'string') direction = orderBy.direction;
          issues.sort((a, b) => (direction === 'DESC' ? b.number - a.number : a.number - b.number));
          return connectionObj('IssueConnection', 'IssueEdge', connectionPage(issues.map((issue) => issueObj(repo, issue)), args));
        }
        case 'pullRequest': {
          const number = typeof args.number === 'number' ? args.number : -1;
          const pull = repo.pulls.get(number);
          return pull === undefined ? null : pullObj(repo, pull);
        }
        case 'pullRequests': {
          let pulls = [...repo.pulls.values()];
          const states = Array.isArray(args.states) ? (args.states as string[]) : ['OPEN'];
          pulls = pulls.filter((pull) => states.includes(pullStateGql(pull)));
          pulls.sort((a, b) => a.number - b.number);
          return connectionObj('PullRequestConnection', 'PullRequestEdge', connectionPage(pulls.map((pull) => pullObj(repo, pull)), args));
        }
        default:
          return fail();
      }
    }
    case 'Ref': {
      if (name === 'name') return obj.name;
      if (name === 'prefix') return 'refs/heads/';
      if (name === 'id') return globalId(`Ref:${(obj.repo as Repo).id}:${String(obj.name)}`);
      if (name === 'target') return { __typename: 'Commit', oid: obj.oid };
      return fail();
    }
    case 'Commit': {
      if (name === 'oid' || name === 'id') return obj.oid;
      return fail();
    }
    case 'Issue': {
      const repo = obj.repo as Repo;
      const issue = obj.issue as IssueRec;
      switch (name) {
        case 'id':
          return issueGlobalId(repo, issue);
        case 'number':
          return issue.number;
        case 'title':
          return issue.title;
        case 'state':
          return issue.state.toUpperCase();
        case 'body':
          return issue.body;
        case 'author':
          return { __typename: 'User', login: VIEWER_LOGIN } satisfies GqlObj;
        case 'repository':
          return repoObj(repo);
        case 'closed':
          return issue.state === 'closed';
        case 'url':
          return `http://forge.invalid/${repo.owner ?? VIEWER_LOGIN}/${repo.name}/issues/${issue.number}`;
        default:
          return fail();
      }
    }
    case 'PullRequest': {
      const repo = obj.repo as Repo;
      const pull = obj.pull as PullRec;
      switch (name) {
        case 'id':
          return pullGlobalId(repo, pull);
        case 'number':
          return pull.number;
        case 'title':
          return pull.title;
        case 'body':
          return pull.body;
        case 'state':
          return pullStateGql(pull);
        case 'merged':
          return pull.merged;
        case 'mergeable': {
          if (pull.merged) return 'UNKNOWN';
          return tryMerge(repo, pull.base, pull.head) !== null ? 'MERGEABLE' : 'CONFLICTING';
        }
        case 'headRefName':
          return pull.head;
        case 'baseRefName':
          return pull.base;
        case 'headRef': {
          const tip = repo.refs.get(`refs/heads/${pull.head}`);
          return tip === undefined ? null : ({ __typename: 'Ref', repo, name: pull.head, oid: tip } satisfies GqlObj);
        }
        case 'baseRef': {
          const tip = repo.refs.get(`refs/heads/${pull.base}`);
          return tip === undefined ? null : ({ __typename: 'Ref', repo, name: pull.base, oid: tip } satisfies GqlObj);
        }
        case 'author':
          return { __typename: 'User', login: VIEWER_LOGIN } satisfies GqlObj;
        case 'repository':
          return repoObj(repo);
        case 'files': {
          const files = pullFilesList(repo, pull).map((file) => ({
            __typename: 'PullRequestChangedFile',
            path: file.path,
            additions: file.additions,
            deletions: file.deletions,
            changeType: file.status.toUpperCase(),
          }) satisfies GqlObj);
          return connectionObj('PullRequestChangedFileConnection', 'PullRequestChangedFileEdge', connectionPage(files, args));
        }
        case 'url':
          return `http://forge.invalid/${repo.owner ?? VIEWER_LOGIN}/${repo.name}/pull/${pull.number}`;
        default:
          return fail();
      }
    }
    case 'IssueConnection':
    case 'PullRequestConnection':
    case 'PullRequestChangedFileConnection': {
      if (name === 'nodes') return obj.nodesRaw;
      if (name === 'totalCount') return obj.totalCount;
      if (name === 'pageInfo') return obj.pageInfo;
      if (name === 'edges') {
        const nodes = obj.nodesRaw as GqlObj[];
        const cursors = obj.cursors as string[];
        return nodes.map((node, i) => ({ __typename: obj.edgeTypename as string, node, cursor: cursors[i] }) satisfies GqlObj);
      }
      return fail();
    }
    case 'IssueEdge':
    case 'PullRequestEdge':
    case 'PullRequestChangedFileEdge':
    case 'IssueCommentEdge': {
      if (name === 'node') return obj.node;
      if (name === 'cursor') return obj.cursor;
      return fail();
    }
    case 'PageInfo': {
      if (name === 'hasNextPage' || name === 'hasPreviousPage' || name === 'startCursor' || name === 'endCursor') return obj[name];
      return fail();
    }
    case 'PullRequestChangedFile': {
      if (name === 'path') return obj.path;
      if (name === 'additions') return obj.additions;
      if (name === 'deletions') return obj.deletions;
      if (name === 'changeType') return obj.changeType;
      return fail();
    }
    case 'IssueComment': {
      if (name === 'id') return obj.id;
      if (name === 'body') return obj.body;
      if (name === 'author') return { __typename: 'User', login: VIEWER_LOGIN } satisfies GqlObj;
      return fail();
    }
    case 'CreateIssuePayload':
    case 'CloseIssuePayload': {
      if (name === 'issue') return obj.issue;
      if (name === 'clientMutationId') return obj.clientMutationId ?? null;
      return fail();
    }
    case 'CreatePullRequestPayload':
    case 'MergePullRequestPayload': {
      if (name === 'pullRequest') return obj.pullRequest;
      if (name === 'clientMutationId') return obj.clientMutationId ?? null;
      return fail();
    }
    case 'AddCommentPayload': {
      if (name === 'commentEdge') return obj.commentEdge;
      if (name === 'subject') return obj.subject ?? null;
      if (name === 'clientMutationId') return obj.clientMutationId ?? null;
      return fail();
    }
    default:
      return fail();
  }
}

/** Look up any node by its global id. */
function nodeByGlobalId(id: string): GqlObj | null {
  const raw = decodeGlobalId(id);
  if (raw === null) return null;
  const parts = raw.split(':');
  if (parts[0] === 'Repository') {
    const repo = repoById(Number.parseInt(parts[1] ?? '', 10));
    return repo === null ? null : repoObj(repo);
  }
  if (parts[0] === 'Issue' || parts[0] === 'PullRequest') {
    const repo = repoById(Number.parseInt(parts[1] ?? '', 10));
    if (repo === null) return null;
    const number = Number.parseInt(parts[2] ?? '', 10);
    if (parts[0] === 'Issue') {
      const issue = repo.issues.get(number);
      return issue === undefined ? null : issueObj(repo, issue);
    }
    const pull = repo.pulls.get(number);
    return pull === undefined ? null : pullObj(repo, pull);
  }
  if (parts[0] === 'User') return { __typename: 'User', login: VIEWER_LOGIN };
  return null;
}

/** Run one mutation field; returns the payload object (errors are collected in ctx). */
function gqlMutation(field: GqlField, ctx: GqlContext): unknown {
  const args = argsOf(field, ctx);
  const input = (args.input ?? {}) as Record<string, unknown>;
  const clientMutationId = typeof input.clientMutationId === 'string' ? input.clientMutationId : null;
  const badInput = (message: string): null => {
    ctx.errors.push({ message });
    return null;
  };

  switch (field.name) {
    case 'createIssue': {
      const repo = typeof input.repositoryId === 'string' ? nodeByGlobalId(input.repositoryId) : null;
      if (repo === null || repo.__typename !== 'Repository') return badInput('repositoryId does not name a repository');
      const target = repo.repo as Repo;
      const title = typeof input.title === 'string' ? input.title : '';
      if (title === '') return badInput('title is required');
      const issue: IssueRec = {
        id: issueIdCounter++,
        number: target.nextNumber++,
        title,
        body: typeof input.body === 'string' ? input.body : '',
        state: 'open',
        labels: [],
        comments: [],
      };
      target.issues.set(issue.number, issue);
      return { __typename: 'CreateIssuePayload', issue: issueObj(target, issue), clientMutationId } satisfies GqlObj;
    }
    case 'closeIssue': {
      const node = typeof input.issueId === 'string' ? nodeByGlobalId(input.issueId) : null;
      if (node === null || node.__typename !== 'Issue') return badInput('issueId does not name an issue');
      const issue = node.issue as IssueRec;
      issue.state = 'closed';
      return { __typename: 'CloseIssuePayload', issue: node, clientMutationId } satisfies GqlObj;
    }
    case 'createPullRequest': {
      const repoNode = typeof input.repositoryId === 'string' ? nodeByGlobalId(input.repositoryId) : null;
      if (repoNode === null || repoNode.__typename !== 'Repository') return badInput('repositoryId does not name a repository');
      const target = repoNode.repo as Repo;
      const head = typeof input.headRefName === 'string' ? input.headRefName : '';
      const base = typeof input.baseRefName === 'string' ? input.baseRefName : '';
      const title = typeof input.title === 'string' ? input.title : '';
      if (target.refs.get(`refs/heads/${head}`) === undefined || target.refs.get(`refs/heads/${base}`) === undefined) {
        return badInput('head or base branch does not exist');
      }
      const pull: PullRec = {
        id: issueIdCounter++,
        number: target.nextNumber++,
        title,
        body: typeof input.body === 'string' ? input.body : '',
        state: 'open',
        head,
        base,
        merged: false,
        mergedAt: null,
        mergeCommitSha: null,
      };
      target.pulls.set(pull.number, pull);
      return { __typename: 'CreatePullRequestPayload', pullRequest: pullObj(target, pull), clientMutationId } satisfies GqlObj;
    }
    case 'mergePullRequest': {
      const node = typeof input.pullRequestId === 'string' ? nodeByGlobalId(input.pullRequestId) : null;
      if (node === null || node.__typename !== 'PullRequest') return badInput('pullRequestId does not name a pull request');
      const repo = node.repo as Repo;
      const pull = node.pull as PullRec;
      if (!pull.merged) {
        const sha = squashMerge(repo, pull);
        if (sha === null) return badInput('Pull Request is not mergeable: conflicts must be resolved first');
        pull.merged = true;
        pull.state = 'closed';
        pull.mergedAt = new Date().toISOString();
        pull.mergeCommitSha = sha;
      }
      return { __typename: 'MergePullRequestPayload', pullRequest: node, clientMutationId } satisfies GqlObj;
    }
    case 'addComment': {
      const node = typeof input.subjectId === 'string' ? nodeByGlobalId(input.subjectId) : null;
      if (node === null || node.__typename !== 'Issue') return badInput('subjectId does not name an issue');
      const repo = node.repo as Repo;
      const issue = node.issue as IssueRec;
      const comment = { id: commentIdCounter++, body: typeof input.body === 'string' ? input.body : '' };
      issue.comments.push(comment);
      const commentObj: GqlObj = {
        __typename: 'IssueComment',
        id: globalId(`IssueComment:${repo.id}:${issue.number}:${comment.id}`),
        body: comment.body,
      };
      return {
        __typename: 'AddCommentPayload',
        commentEdge: { __typename: 'IssueCommentEdge', node: commentObj, cursor: cursorOf(issue.comments.length - 1) } satisfies GqlObj,
        subject: node,
        clientMutationId,
      } satisfies GqlObj;
    }
    default:
      throw new GqlFieldError(`Field '${field.name}' doesn't exist on type 'Mutation'`);
  }
}

/** Complete a resolved value against a selection set into plain JSON. */
function gqlComplete(value: unknown, selection: GqlSelection[] | null, ctx: GqlContext, rootType: string): unknown {
  if (value === null || value === undefined) return null;
  if (Array.isArray(value)) return value.map((item) => gqlComplete(item, selection, ctx, rootType));
  if (typeof value !== 'object') return value;
  const obj = value as GqlObj;
  if (selection === null) return null;
  const out: Record<string, unknown> = {};
  const applySelections = (selections: GqlSelection[], target: GqlObj): void => {
    for (const item of selections) {
      if (item.kind === 'inline') {
        if (item.typeCondition === null || item.typeCondition === target.__typename) applySelections(item.selection, target);
        continue;
      }
      if (item.kind === 'spread') {
        const fragment = ctx.fragments.get(item.name);
        if (fragment !== undefined) applySelections(fragment, target);
        continue;
      }
      const field = item.field;
      const key = field.alias ?? field.name;
      if (field.name === '__typename') {
        out[key] = target.__typename;
        continue;
      }
      try {
        const resolved =
          target.__typename === 'Mutation'
            ? gqlMutation(field, ctx)
            : gqlField(target, field, ctx);
        out[key] = gqlComplete(resolved, field.selection, ctx, rootType);
      } catch (err) {
        if (err instanceof GqlFieldError) {
          ctx.errors.push({ message: err.message });
          out[key] = null;
        } else {
          throw err;
        }
      }
    }
  };
  applySelections(selection, obj);
  return out;
}

/** Execute one parsed operation; returns the response envelope. */
function executeGraphql(
  document: GqlDocument,
  operationName: string | null,
  variables: Record<string, unknown>,
): Record<string, unknown> {
  const operation =
    operationName === null
      ? document.operations[0]
      : document.operations.find((candidate) => candidate.name === operationName) ?? document.operations[0];
  if (operation === undefined) return { errors: [{ message: 'No operation in document' }] };
  const ctx: GqlContext = { variables, fragments: document.fragments, errors: [] };
  const root: GqlObj = { __typename: operation.type === 'mutation' ? 'Mutation' : 'Query' };
  const data = gqlComplete(root, operation.selection, ctx, root.__typename);
  const envelope: Record<string, unknown> = { data };
  if (ctx.errors.length > 0) envelope.errors = ctx.errors;
  return envelope;
}

async function handleGraphql(req: IncomingMessage, res: ServerResponse): Promise<void> {
  if (!bearerOk(req)) {
    sendJson(res, 401, { message: 'Bad credentials' });
    return;
  }
  const raw = await readBody(req);
  let parsed: unknown;
  try {
    parsed = JSON.parse(raw.toString('utf8'));
  } catch {
    sendJson(res, 400, { errors: [{ message: 'Malformed JSON in request body' }] });
    return;
  }
  const executeOne = (entry: unknown): Record<string, unknown> => {
    if (typeof entry !== 'object' || entry === null) return { errors: [{ message: 'Invalid GraphQL request' }] };
    const request = entry as { query?: unknown; variables?: unknown; operationName?: unknown };
    if (typeof request.query !== 'string') return { errors: [{ message: 'No query in request' }] };
    let document: GqlDocument;
    try {
      document = parseGraphql(request.query);
    } catch (err) {
      return { data: null, errors: [{ message: err instanceof Error ? err.message : 'Syntax error' }] };
    }
    const variables =
      typeof request.variables === 'object' && request.variables !== null && !Array.isArray(request.variables)
        ? (request.variables as Record<string, unknown>)
        : {};
    return executeGraphql(document, typeof request.operationName === 'string' ? request.operationName : null, variables);
  };
  if (Array.isArray(parsed)) {
    sendJson(res, 200, parsed.map(executeOne));
    return;
  }
  sendJson(res, 200, executeOne(parsed));
}

// ---------------------------------------------------------------------------
// MCP endpoint (streamable HTTP JSON-RPC over the same store)

const MCP_TOOLS = [
  {
    name: 'create_repo',
    description: 'Create a new repository owned by the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'The repository name.' },
        description: { type: 'string', description: 'A short description of the repository.' },
        private: { type: 'boolean', description: 'Whether the repository is private.' },
      },
      required: ['name'],
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The issue title.' },
        body: { type: 'string', description: 'The issue body.' },
      },
      required: ['owner', 'repo', 'title'],
    },
  },
  {
    name: 'list_issues',
    description: 'List the issues of a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        state: { type: 'string', description: 'Filter by state: open, closed or all.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request from a head branch into a base branch.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The pull request title.' },
        head: { type: 'string', description: 'The head branch name.' },
        base: { type: 'string', description: 'The base branch name.' },
        body: { type: 'string', description: 'The pull request body.' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request into its base branch.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        pull_number: { type: 'integer', description: 'The pull request number.' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
] as const;

interface McpRpcError {
  code: number;
  message: string;
}

function mcpToolResult(value: unknown): Record<string, unknown> {
  return {
    content: [{ type: 'text', text: typeof value === 'string' ? value : JSON.stringify(value) }],
    structuredContent: value,
  };
}

function mcpToolError(message: string): Record<string, unknown> {
  return { content: [{ type: 'text', text: message }], isError: true };
}

/** Run one MCP tool against the shared store. Throws McpRpcError-shaped objects for protocol errors. */
function runMcpTool(name: string, args: Record<string, unknown>): Record<string, unknown> {
  const need = (key: string): unknown => {
    const value = args[key];
    if (value === undefined || value === null) throw { code: -32602, message: `missing required argument: ${key}` } as McpRpcError;
    return value;
  };
  const repoOf = (): Repo => {
    const owner = String(need('owner'));
    const repoName = String(need('repo'));
    const repo = findRepo(owner, repoName);
    if (repo === null) throw { code: -32602, message: `repository ${owner}/${repoName} not found` } as McpRpcError;
    return repo;
  };

  switch (name) {
    case 'create_repo': {
      const repoName = String(need('name'));
      if (repos.has(repoName)) return mcpToolError(`repository ${repoName} already exists`);
      const repo = createRepoRec(
        repoName,
        typeof args.description === 'string' ? args.description : '',
        typeof args.private === 'boolean' ? args.private : false,
      );
      repo.owner = VIEWER_LOGIN;
      return mcpToolResult(repoJson(repo));
    }
    case 'get_repo': {
      return mcpToolResult(repoJson(repoOf()));
    }
    case 'create_issue': {
      const repo = repoOf();
      const title = String(need('title'));
      const issue: IssueRec = {
        id: issueIdCounter++,
        number: repo.nextNumber++,
        title,
        body: typeof args.body === 'string' ? args.body : '',
        state: 'open',
        labels: [],
        comments: [],
      };
      repo.issues.set(issue.number, issue);
      return mcpToolResult(issueJson(repo, issue));
    }
    case 'list_issues': {
      const repo = repoOf();
      const state = typeof args.state === 'string' ? args.state : 'open';
      const items = [...repo.issues.values()]
        .filter((issue) => state === 'all' || issue.state === state)
        .map((issue) => issueJson(repo, issue));
      return mcpToolResult(items);
    }
    case 'create_pull_request': {
      const repo = repoOf();
      const title = String(need('title'));
      const head = String(need('head'));
      const base = String(need('base'));
      if (repo.refs.get(`refs/heads/${head}`) === undefined || repo.refs.get(`refs/heads/${base}`) === undefined) {
        return mcpToolError('head or base branch does not exist');
      }
      const pull: PullRec = {
        id: issueIdCounter++,
        number: repo.nextNumber++,
        title,
        body: typeof args.body === 'string' ? args.body : '',
        state: 'open',
        head,
        base,
        merged: false,
        mergedAt: null,
        mergeCommitSha: null,
      };
      repo.pulls.set(pull.number, pull);
      return mcpToolResult(pullJson(repo, pull));
    }
    case 'merge_pull_request': {
      const repo = repoOf();
      const number = Number(need('pull_number'));
      const pull = repo.pulls.get(number);
      if (pull === undefined) return mcpToolError(`pull request ${number} not found`);
      if (!pull.merged) {
        const sha = squashMerge(repo, pull);
        if (sha === null) return mcpToolError('Pull Request is not mergeable: conflicts must be resolved first');
        pull.merged = true;
        pull.state = 'closed';
        pull.mergedAt = new Date().toISOString();
        pull.mergeCommitSha = sha;
      }
      return mcpToolResult(pullJson(repo, pull));
    }
    default:
      throw { code: -32601, message: `unknown tool: ${name}` } as McpRpcError;
  }
}

async function handleMcp(req: IncomingMessage, res: ServerResponse): Promise<void> {
  if (req.method !== 'POST') {
    sendJson(res, 405, { message: 'Method Not Allowed' });
    return;
  }
  const raw = await readBody(req);
  let parsed: unknown;
  try {
    parsed = JSON.parse(raw.toString('utf8'));
  } catch {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return;
  }

  const handleOne = (entry: unknown): Record<string, unknown> | null => {
    if (typeof entry !== 'object' || entry === null) {
      return { jsonrpc: '2.0', id: null, error: { code: -32600, message: 'Invalid Request' } };
    }
    const request = entry as { id?: unknown; method?: unknown; params?: unknown };
    const isNotification = request.id === undefined;
    if (isNotification) return null;
    const id = request.id ?? null;
    const method = typeof request.method === 'string' ? request.method : '';
    const params = (typeof request.params === 'object' && request.params !== null ? request.params : {}) as Record<string, unknown>;
    try {
      switch (method) {
        case 'server/discover':
          return {
            jsonrpc: '2.0',
            id,
            result: {
              supportedVersions: ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26'],
              capabilities: { tools: {} },
              serverInfo: { name: 'forge', version: FORGE_VERSION },
            },
          };
        case 'initialize':
          return {
            jsonrpc: '2.0',
            id,
            result: {
              protocolVersion: typeof params.protocolVersion === 'string' ? params.protocolVersion : '2025-11-25',
              capabilities: { tools: {} },
              serverInfo: { name: 'forge', version: FORGE_VERSION },
            },
          };
        case 'tools/list':
          return { jsonrpc: '2.0', id, result: { tools: MCP_TOOLS } };
        case 'tools/call': {
          const toolName = typeof params.name === 'string' ? params.name : '';
          const toolArgs = (typeof params.arguments === 'object' && params.arguments !== null ? params.arguments : {}) as Record<string, unknown>;
          return { jsonrpc: '2.0', id, result: runMcpTool(toolName, toolArgs) };
        }
        case 'ping':
          return { jsonrpc: '2.0', id, result: {} };
        default:
          return { jsonrpc: '2.0', id, error: { code: -32601, message: `Method not found: ${method}` } };
      }
    } catch (err) {
      const rpcError = err as McpRpcError;
      if (typeof rpcError?.code === 'number') {
        return { jsonrpc: '2.0', id, error: { code: rpcError.code, message: rpcError.message } };
      }
      throw err;
    }
  };

  const entries = Array.isArray(parsed) ? parsed : [parsed];
  // Auth is checked before any tool runs; notifications carry no id and need no answer.
  const hasRequest = entries.some((entry) => typeof entry === 'object' && entry !== null && (entry as { id?: unknown }).id !== undefined);
  if (hasRequest && !bearerOk(req)) {
    sendJson(res, 401, { message: 'Unauthorized' });
    return;
  }
  const responses = entries.map(handleOne).filter((entry) => entry !== null);
  if (responses.length === 0) {
    res.writeHead(202, { 'content-length': 0 });
    res.end();
    return;
  }
  sendJson(res, 200, Array.isArray(parsed) ? responses : responses[0]);
}

// ---------------------------------------------------------------------------
// The server

const GIT_ROUTE = /^\/([^/]+)\/([^/]+)\.git\/(info\/refs|git-upload-pack|git-receive-pack)$/;

async function route(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const url = new URL(req.url ?? '/', 'http://entry');
  const path = url.pathname;
  const method = req.method ?? 'GET';

  if (method === 'GET' && path === '/healthz') {
    sendJson(res, 200, { ok: true });
    return;
  }

  const gitMatch = GIT_ROUTE.exec(path);
  if (gitMatch !== null) {
    const owner = decodeURIComponent(gitMatch[1]!);
    const repo = findRepo(owner, decodeURIComponent(gitMatch[2]!));
    if (repo === null) {
      notFound(res);
      return;
    }
    if (!bearerOk(req)) {
      sendJson(res, 401, { message: 'Bad credentials' });
      return;
    }
    const service = gitMatch[3]!;
    if (method === 'GET' && service === 'info/refs') {
      handleInfoRefs(req, res, repo, url);
      return;
    }
    if (method === 'POST' && service === 'git-upload-pack') {
      await handleUploadPack(res, repo, await readBody(req));
      return;
    }
    if (method === 'POST' && service === 'git-receive-pack') {
      await handleReceivePack(res, repo, await readBody(req));
      return;
    }
    notFound(res);
    return;
  }

  if (path === '/api/graphql') {
    if (method !== 'POST') {
      notFound(res);
      return;
    }
    await handleGraphql(req, res);
    return;
  }

  if (path === '/mcp') {
    await handleMcp(req, res);
    return;
  }

  if (path === '/api/v3' || path.startsWith('/api/v3/')) {
    await handleRest(req, res, url);
    return;
  }

  notFound(res);
}

/** Build the forge server. It binds nothing until the caller listens. */
export function createApp(): Server {
  return createServer((req: IncomingMessage, res: ServerResponse) => {
    route(req, res).catch(() => {
      if (!res.headersSent) sendJson(res, 500, { message: 'Internal Server Error' });
      else res.end();
    });
  });
}
