# Kontainer Deployment Checklist (KONOMI v0)

This checklist is for **deployment hygiene** (not compliance certification).

## Secrets & access
- [ ] API key stored as secret (not committed)
- [ ] Least privilege: non-root container user
- [ ] Network exposure restricted (bind/ingress only where needed)

## Observability
- [ ] Structured logs (request id, timestamp, endpoint, status)
- [ ] Health endpoint monitored
- [ ] Basic rate limiting enabled (gateway preferred in production)

## Reliability
- [ ] Resource limits set (CPU/RAM)
- [ ] Restart policy / liveness probes configured
- [ ] Rollback procedure documented

## Reproducibility
- [ ] Image pinned by digest/tag
- [ ] Git commit recorded in build metadata
- [ ] SBOM / dependency list available (optional)

## Safety note
This repository includes research scaffolds. Do not expose public endpoints without a security review.
