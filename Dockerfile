# Adapted from https://github.com/akabe/docker-ocaml/blob/master/dockerfiles/ubuntu16.04_ocaml4.06.1/Dockerfile

FROM ubuntu:18.04

LABEL maintainer="padhi@cs.ucla.edu"


ENV OPAM_VERSION  2.0.4
ENV OCAML_VERSION 4.08.0+flambda
ENV Z3_VERSION    Z3-4.8.5

ENV HOME /home/opam


ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
    apt-get upgrade -yq && \
    apt-get install -yq aspcud \
                        binutils \
                        cmake curl \
                        g++ git \
                        libgmp-dev libgomp1 libomp5 libomp-dev libx11-dev \
                        m4 make \
                        patch python3 python3-distutils \
                        sudo \
                        time tzdata \
                        unzip && \
    apt-get autoremove -y --purge


RUN adduser --disabled-password --home $HOME --shell /bin/bash --gecos '' opam && \
    echo 'opam ALL=(ALL) NOPASSWD:ALL' >>/etc/sudoers && \
    curl -L -o /usr/bin/opam "https://github.com/ocaml/opam/releases/download/$OPAM_VERSION/opam-$OPAM_VERSION-$(uname -m)-$(uname -s)" && \
    chmod 755 /usr/bin/opam && \
    su opam -c "opam init --auto-setup --disable-sandboxing --yes --compiler=$OCAML_VERSION && opam clean"


USER opam
WORKDIR $HOME


RUN opam install --yes alcotest.0.8.5       \
                       async.v0.12.0        \
                       core.v0.12.2         \
                       dune.1.10.0          \
                       ppx_let.v0.12.0 &&   \
    opam clean --yes && \
    git clone https://github.com/SaswatPadhi/LoopInvGen.git LoopInvGen


WORKDIR $HOME/LoopInvGen


ENV LC_CTYPE=C.UTF-8
RUN curl -LO https://github.com/Z3Prover/z3/archive/$Z3_VERSION.zip && \
    unzip $Z3_VERSION.zip && \
    opam config exec -- ./scripts/build_all.sh --with-logging --build-z3 z3-$Z3_VERSION && \
    rm -rf z3*


ENTRYPOINT [ "opam", "config", "exec", "--" ]
CMD [ "bash" ]
