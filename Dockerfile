# Adapted from https://github.com/akabe/docker-ocaml/blob/master/dockerfiles/ubuntu16.04_ocaml4.06.1/Dockerfile

FROM ubuntu:18.04

LABEL maintainer="padhi@cs.ucla.edu"


ENV OPAM_VERSION  2.0.0
ENV OCAML_VERSION 4.07.1+flambda
ENV Z3_VERSION    4.8.1

ENV HOME /home/opam


ARG DEBIAN_FRONTEND=noninteractive
RUN apt update && \
    apt upgrade -yq && \
    apt install -yq aspcud binutils cmake curl g++ git libgmp-dev libgomp1 libomp5 \
                    libomp-dev libx11-dev m4 make patch python2.7 sudo tzdata unzip
RUN apt autoremove -y --purge && \
    apt autoclean


RUN adduser --disabled-password --home $HOME --shell /bin/bash --gecos '' opam && \
    echo 'opam ALL=(ALL) NOPASSWD:ALL' >>/etc/sudoers


RUN curl -L -o /usr/bin/opam "https://github.com/ocaml/opam/releases/download/$OPAM_VERSION/opam-$OPAM_VERSION-$(uname -m)-$(uname -s)" && \
    chmod 755 /usr/bin/opam
RUN su opam -c "opam init --auto-setup --disable-sandboxing --yes --compiler=$OCAML_VERSION"


USER opam
WORKDIR $HOME


RUN opam install --yes alcotest.0.8.4 core.v0.11.3 core_extended.v0.11.0 dune.1.5.1
RUN opam clean --yes


RUN curl -LO https://github.com/Z3Prover/z3/archive/z3-$Z3_VERSION.zip && \
    unzip z3-$Z3_VERSION.zip && mv z3-z3-$Z3_VERSION z3-$Z3_VERSION
RUN git clone https://github.com/SaswatPadhi/LoopInvGen.git LoopInvGen


WORKDIR $HOME/LoopInvGen


RUN opam config exec -- ./build_all.sh --with-logging --build-z3 $HOME/z3-$Z3_VERSION


ENTRYPOINT [ "opam", "config", "exec", "--" ]
CMD [ "bash" ]
