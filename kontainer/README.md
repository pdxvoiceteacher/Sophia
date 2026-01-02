# Kontainer (KONOMI v0)

This folder contains deployment scaffolding (Docker/K8s) and checklists.
It is meant for **demo and review**, not production hardening.

## Quick run (Docker Compose)

1) Copy env file:
- `copy kontainer\.env.example kontainer\.env`

2) Run:
- `docker compose -f kontainer/docker-compose.kontainer.yml --env-file kontainer/.env up --build`

3) Test:
- Health: `http://127.0.0.1:8000/health`
- Process: POST `/v0/process` with header `X-API-Key`

## Kubernetes (example)
See `kontainer/k8s/` for deployment/service/secret examples.

## UCC
A UCC checklist exists at:
- `ucc/modules/kontainer_deploy_coverage.yml`
- `ucc/tasks/kontainer_deploy_task.json`

Run:
`python -m ucc.cli run ucc/modules/kontainer_deploy_coverage.yml --input ucc/tasks/kontainer_deploy_task.json --outdir ucc/out/kontainer_demo`
