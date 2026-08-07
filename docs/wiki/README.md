# ECHIDNA Wiki — Source Pages

These six files are the **source of truth** for the GitHub wiki at
<https://github.com/hyperpolymath/echidna/wiki>. The wiki lives in a separate
repository (`echidna.wiki.git`); edit the pages here, then sync.

**Syncing is scriptable** — an earlier note in this file claimed the wiki was
not pushable from automation. It is: `echidna.wiki.git` accepts a normal clone
and push with the same credentials as the main repository. Its default branch
is `master`, not `main`.

```bash
git clone https://github.com/hyperpolymath/echidna.wiki.git /tmp/echidna-wiki
for f in Home Architecture Getting-Started FAQ Guides Troubleshooting; do
  cp docs/wiki/"$f".md /tmp/echidna-wiki/"$f".md
done
git -C /tmp/echidna-wiki add -A
git -C /tmp/echidna-wiki commit -m "docs: sync wiki from docs/wiki/"
git -C /tmp/echidna-wiki push origin master
```

Wiki pages are flat — there is no nesting, and the filename is the page name.
Editing a page in the GitHub web UI bypasses this directory and will be
overwritten by the next sync, so make changes here.

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
