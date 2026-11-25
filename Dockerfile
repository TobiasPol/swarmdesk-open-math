FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
    bubblewrap \
    ca-certificates \
    curl \
    git \
    gnupg \
    jq \
    xz-utils \
    zstd \
  && mkdir -p /etc/apt/keyrings \
  && curl -fsSL https://cli.github.com/packages/githubcli-archive-keyring.gpg \
     -o /etc/apt/keyrings/githubcli-archive-keyring.gpg \
  && chmod go+r /etc/apt/keyrings/githubcli-archive-keyring.gpg \
  && echo "deb [arch=$(dpkg --print-architecture) signed-by=/etc/apt/keyrings/githubcli-archive-keyring.gpg] https://cli.github.com/packages stable main" \
     > /etc/apt/sources.list.d/github-cli.list \
  && curl -fsSL https://deb.nodesource.com/setup_22.x | bash - \
  && apt-get update && apt-get install -y --no-install-recommends \
    gh \
    nodejs \
  && rm -rf /var/lib/apt/lists/*

# Replace Ubuntu's default UID 1000 user with non-root `agent` user
RUN userdel -r ubuntu 2>/dev/null || true \
  && useradd -m -u 1000 -s /bin/bash agent \
  && mkdir -p /workspace \
  && chown -R agent:agent /workspace

USER agent
WORKDIR /workspace

ENV ELAN_HOME="/home/agent/.elan"
ENV PATH="/home/agent/.elan/bin:${PATH}"

COPY --chown=agent:agent lean-toolchain /tmp/lean-toolchain
RUN TOOLCHAIN="$(tr -d '[:space:]' < /tmp/lean-toolchain)" \
  && curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
     | sh -s -- -y --default-toolchain "${TOOLCHAIN}" \
  && rm -f /tmp/lean-toolchain

COPY --chown=agent:agent . /workspace

RUN lake exe cache get && lake build sdlean_verify
