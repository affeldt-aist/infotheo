# ============================================================
# Stage 1: Install dependencies
# ============================================================
FROM ocaml/opam:alpine-3.21-ocaml-4.14 AS deps

RUN sudo apk add --no-cache clang gmp-dev pkgconf linux-headers

RUN opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam update

WORKDIR /home/opam/infotheo
COPY --chown=opam:opam coq-infotheo.opam .
RUN opam install --deps-only -y -j"$(nproc)" ./coq-infotheo.opam && \
    opam clean -a -c -s --logs

# ============================================================
# Stage 2: Build
# ============================================================
FROM deps AS build

COPY --chown=opam:opam . .
CMD ["sh", "-c", "opam exec -- make -j\"$(nproc)\""]
