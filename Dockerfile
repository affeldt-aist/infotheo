# ============================================================
# Stage 1: Install dependencies
# ============================================================
FROM ocaml/opam:ubuntu-24.04-ocaml-4.14 AS deps

RUN sudo apt-get update && \
    sudo apt-get install -y --no-install-recommends clang libgmp-dev pkg-config && \
    sudo rm -rf /var/lib/apt/lists/*

RUN opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam update

WORKDIR /home/opam/infotheo
COPY --chown=opam:opam coq-infotheo.opam .
# nproc is available as a shell command in most Linux distributions, provided by coreutils.
# In this image (ubuntu-24.04), it should be available by default.
# You can check with: which nproc
RUN opam install --deps-only -y -j"$(nproc)" ./coq-infotheo.opam

# ============================================================
# Stage 2: Build
# ============================================================
FROM deps AS build

COPY --chown=opam:opam . .
CMD opam exec -- make -j"$(nproc)"
