# Sophia Standards Deployment Notes

This document describes a minimal deployment for publishing the Sophia standards artifacts and the
Run Viewer.

## Paths

- **Viewer**: `https://ultraverbaluxmentis.org/sophia/viewer` (static `web/` build)
- **Standards API**: `https://ultraverbaluxmentis.org/sophia/api`

## Reverse Proxy Sketch (NGINX)

```
location /sophia/viewer/ {
  alias /var/www/sophia/web/;
  try_files $uri $uri/ /sophia/viewer/index.html;
<<<<<<< HEAD
  add_header Cache-Control "public, max-age=3600";
=======
>>>>>>> origin/main
}

location /sophia/api/ {
  proxy_pass http://127.0.0.1:8001/;
  proxy_set_header Host $host;
  proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
  proxy_set_header X-Forwarded-Proto $scheme;
}
```

## Standards Gateway

Run locally:

```
python -m uvicorn tools.sophia.standards_api:app --port 8001
```

Verify discovery:

- `https://ultraverbaluxmentis.org/sophia/api/.well-known/sophia.json`
- `https://ultraverbaluxmentis.org/sophia/api/manifest.json`
<<<<<<< HEAD
- `https://ultraverbaluxmentis.org/sophia/api/healthz`
=======
>>>>>>> origin/main
