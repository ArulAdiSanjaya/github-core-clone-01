[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/ArulAdiSanjaya/github-core-clone-01/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/ArulAdiSanjaya/github-core-clone-01/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

# Forge — a GitHub-compatible git forge

Entry for make.fun's ["Build a GitHub-compatible git forge" bounty](https://make.fun/bounty/github-core-clone-01).

A single-file, dependency-free TypeScript server (Node ≥ 22, standard library only) that
implements the GitHub-compatible surface the bounty grades:

- **Git smart HTTP** — protocol v2 (`ls-refs`, `fetch` with shallow/deepen support) and
  protocol v0 advertisements, clone/fetch/push over `git-upload-pack` / `git-receive-pack`
  with pkt-line framing, sideband pack transfer, report-status, fast-forward enforcement
  and a real SHA-1 object store (commits, trees, blobs, annotated tags).
- **REST API v3** — repositories (create/read/update/delete, paginated listing), contents
  API backed by the same object store, branches and git refs, labels, issues with comments,
  and pull requests with tree-diff file lists and squash merges.
- **GraphQL API v4** — viewer/repository/node queries, issue & pull-request connections
  with cursor pagination, introspection, and the create/close/merge mutations.
- **MCP endpoint** — streamable-HTTP JSON-RPC with `server/discover`, `tools/list` and the
  six canonical forge tools, all reading and writing the same in-memory store as REST,
  GraphQL and git.

Everything lives in memory: one object store and one ref space shared by all four
surfaces, so an object pushed over git is immediately visible through the contents API,
GraphQL and MCP.

## Running

```sh
node --experimental-strip-types main.ts   # needs MAKEFUN_ENV_URL, per the bounty kit
```

`main.ts` is the harness lifecycle (register the bound port, poll `/done`, exit 0);
`app.ts` builds the forge server itself.

## License

MIT — see [LICENSE](LICENSE).
