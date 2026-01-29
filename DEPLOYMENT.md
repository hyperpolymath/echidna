# ECHIDNA Deployment Guide

**Deploy ECHIDNA to production environments**

## Table of Contents

1. [Quick Deploy](#quick-deploy)
2. [Docker Deployment](#docker-deployment)
3. [System Service](#system-service)
4. [Cloud Deployment](#cloud-deployment)
5. [Security Considerations](#security-considerations)

---

## Quick Deploy

### Prerequisites

- Linux server (Ubuntu 22.04+ recommended)
- 2GB RAM minimum
- 10GB disk space
- Rust, Julia, Python 3 installed

### One-Command Deploy

```bash
# Clone repository
git clone https://github.com/hyperpolymath/echidna
cd echidna

# Build production
./build-production.sh

# Deploy
cd dist/echidna
./start.sh
```

Access at `http://your-server:3000`

---

## Docker Deployment

### Dockerfile (Coming Soon)

```dockerfile
FROM rust:1.75 as rust-builder
WORKDIR /app
COPY . .
RUN cargo build --release

FROM julia:1.9 as julia-builder
WORKDIR /app
COPY src/julia /app/julia
RUN julia --project=julia -e 'using Pkg; Pkg.instantiate()'

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y python3 ca-certificates
COPY --from=rust-builder /app/target/release/echidna /usr/local/bin/
COPY --from=julia-builder /app/models /app/models
COPY src/rescript/index.html /app/ui/
COPY src/rescript/src/*.bs.js /app/ui/

EXPOSE 8080 3000
CMD ["/usr/local/bin/echidna", "server", "--port", "8080", "--host", "0.0.0.0", "--cors"]
```

### Docker Compose

```yaml
version: '3.8'

services:
  echidna-backend:
    build: .
    ports:
      - "8080:8080"
    environment:
      - RUST_LOG=info
    volumes:
      - ./models:/app/models

  echidna-frontend:
    image: python:3.11-slim
    working_dir: /app/ui
    volumes:
      - ./dist/echidna/ui:/app/ui
    ports:
      - "3000:3000"
    command: python3 -m http.server 3000
```

---

## System Service

### Systemd Service

Create `/etc/systemd/system/echidna.service`:

```ini
[Unit]
Description=ECHIDNA Theorem Proving Platform
After=network.target

[Service]
Type=simple
User=echidna
WorkingDirectory=/opt/echidna
ExecStart=/opt/echidna/bin/echidna server --port 8080 --host 0.0.0.0 --cors
Restart=always
RestartSec=10

[Install]
WantedBy=multi-user.target
```

Enable and start:

```bash
sudo systemctl daemon-reload
sudo systemctl enable echidna
sudo systemctl start echidna
sudo systemctl status echidna
```

---

## Cloud Deployment

### AWS EC2

```bash
# Launch EC2 instance (t3.medium recommended)
# Ubuntu 22.04 AMI

# Install dependencies
sudo apt update
sudo apt install -y build-essential pkg-config libssl-dev

# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source $HOME/.cargo/env

# Install Julia
wget https://julialang-s3.julialang.org/bin/linux/x64/1.9/julia-1.9.4-linux-x86_64.tar.gz
tar xzf julia-1.9.4-linux-x86_64.tar.gz
sudo ln -s $(pwd)/julia-1.9.4/bin/julia /usr/local/bin/

# Deploy ECHIDNA
git clone https://github.com/hyperpolymath/echidna
cd echidna
./build-production.sh

# Configure firewall
sudo ufw allow 8080/tcp
sudo ufw allow 3000/tcp
```

### DigitalOcean Droplet

Same as AWS EC2 - use Ubuntu 22.04 droplet.

### Google Cloud Platform

```bash
# Create Compute Engine instance
gcloud compute instances create echidna \
  --image-family=ubuntu-2204-lts \
  --image-project=ubuntu-os-cloud \
  --machine-type=e2-medium \
  --zone=us-central1-a

# SSH and follow EC2 instructions above
```

---

## Nginx Reverse Proxy

### Configuration

```nginx
server {
    listen 80;
    server_name echidna.yourdomain.com;

    # Frontend
    location / {
        proxy_pass http://127.0.0.1:3000;
        proxy_http_version 1.1;
        proxy_set_header Upgrade $http_upgrade;
        proxy_set_header Connection 'upgrade';
        proxy_set_header Host $host;
        proxy_cache_bypass $http_upgrade;
    }

    # Backend API
    location /api/ {
        proxy_pass http://127.0.0.1:8080/api/;
        proxy_http_version 1.1;
        proxy_set_header Upgrade $http_upgrade;
        proxy_set_header Connection 'upgrade';
        proxy_set_header Host $host;
        proxy_cache_bypass $http_upgrade;
        
        # CORS headers (if not handled by backend)
        add_header 'Access-Control-Allow-Origin' '*';
        add_header 'Access-Control-Allow-Methods' 'GET, POST, OPTIONS';
    }

    # WebSocket (future)
    location /ws/ {
        proxy_pass http://127.0.0.1:8080/ws/;
        proxy_http_version 1.1;
        proxy_set_header Upgrade $http_upgrade;
        proxy_set_header Connection "upgrade";
        proxy_set_header Host $host;
    }
}
```

### SSL with Let's Encrypt

```bash
sudo apt install certbot python3-certbot-nginx
sudo certbot --nginx -d echidna.yourdomain.com
```

---

## Security Considerations

### API Security

1. **Rate Limiting**: Implement rate limiting on API endpoints
2. **Authentication**: Add JWT or API key authentication
3. **HTTPS Only**: Always use HTTPS in production
4. **CORS**: Configure CORS for specific origins only

### Firewall Rules

```bash
# Allow only necessary ports
sudo ufw default deny incoming
sudo ufw default allow outgoing
sudo ufw allow ssh
sudo ufw allow 80/tcp
sudo ufw allow 443/tcp
sudo ufw enable
```

### Environment Variables

```bash
# Set in .env or systemd service
export ECHIDNA_API_KEY=your-secret-key
export RUST_LOG=info
export ECHIDNA_MAX_SESSIONS=100
```

---

## Monitoring

### Health Check

```bash
# Add to monitoring system
curl http://localhost:8080/api/health

# Expected response:
# {"status":"ok","version":"1.0.0"}
```

### Logs

```bash
# Systemd logs
sudo journalctl -u echidna -f

# Application logs
tail -f /var/log/echidna/app.log
```

### Metrics (Future)

- Prometheus integration planned
- Grafana dashboards coming soon

---

## Scaling

### Horizontal Scaling

1. Run multiple backend instances
2. Use load balancer (Nginx, HAProxy)
3. Shared session storage (Redis)

### Vertical Scaling

- Increase RAM for more concurrent sessions
- Add CPU cores for parallel proof checking
- Use SSD for faster ML model loading

---

## Backup & Recovery

### Backup Strategy

```bash
# Backup models
tar czf models-$(date +%Y%m%d).tar.gz models/

# Backup configuration
cp -r /opt/echidna/config /backup/

# Backup examples
tar czf examples-$(date +%Y%m%d).tar.gz examples/
```

### Recovery

```bash
# Restore from backup
tar xzf models-20260129.tar.gz -C /opt/echidna/
sudo systemctl restart echidna
```

---

## Troubleshooting

### Service Won't Start

```bash
# Check logs
sudo journalctl -u echidna -n 50

# Check port availability
sudo netstat -tlnp | grep 8080

# Verify binary
/opt/echidna/bin/echidna --version
```

### High Memory Usage

```bash
# Check memory
free -h

# Limit sessions
export ECHIDNA_MAX_SESSIONS=50

# Restart service
sudo systemctl restart echidna
```

### Slow Response

- Check CPU usage: `top`
- Optimize Julia models
- Add caching layer
- Scale horizontally

---

## Support

- **Issues**: https://github.com/hyperpolymath/echidna/issues
- **Docs**: https://echidna.docs.org
- **Community**: Join our Discord

---

**Happy Deploying! 🦔**
