# Invariant Path Integration (Echidna)

Echidna wrapper script:

```bash
./scripts/invariant-path.sh scan --file ./README.adoc --artifact-uri repo://README.adoc --write
```

Via `just` from repo root:

```bash
just invariant-path scan --file ./README.adoc --artifact-uri repo://README.adoc --write
```

Default profile: `echidna`

Focus:
- theorem -> guarantee
- assumption-bound -> general truth
- local result -> universal claim

Store path defaults to `.invariant-path/` in the current working directory.

Desktop/start-menu launcher for shared tooling:
- `/var/mnt/eclipse/repos/.desktop-tools/invariant-path-launcher.sh`
