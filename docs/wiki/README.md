# ECHIDNA Wiki — Source Pages

These six files mirror what the GitHub wiki at <https://github.com/hyperpolymath/echidna/wiki>
should display. The wiki repo (`echidna.wiki.git`) sits outside the main
repository and is not pushable from automation in this session, so the
canonical wiki content lives here and is synced manually by an editor with
push rights.

To sync: paste each file's body (everything after the H1) into the matching
wiki page via the GitHub web UI, or `git clone https://github.com/hyperpolymath/echidna.wiki.git`
and copy these files directly. Wiki pages are flat — there is no nesting.

| Wiki page | Source file |
|---|---|
| `Home` | [`Home.md`](Home.md) |
| `Architecture` | [`Architecture.md`](Architecture.md) |
| `Getting-Started` | [`Getting-Started.md`](Getting-Started.md) |
| `FAQ` | [`FAQ.md`](FAQ.md) |
| `Guides` | [`Guides.md`](Guides.md) |
| `Troubleshooting` | [`Troubleshooting.md`](Troubleshooting.md) |

When a wiki page diverges from the matching repo doc it references (e.g.
`docs/ARCHITECTURE.md`), update **the repo doc first**, then refresh the
wiki page from the new repo state. The wiki is a navigation aid; the repo
is the source of truth.
