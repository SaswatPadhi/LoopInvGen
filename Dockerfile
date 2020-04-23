# Adapted from https://github.com/akabe/docker-ocaml/blob/master/dockerfiles/ubuntu16.04_ocaml4.06.1/Dockerfile

FROM ubuntu:18.04

LABEL maintainer="padhi@cs.ucla.edu"


ENV OPAM_VERSION  2.0.6
ENV OCAML_VERSION 4.10.0+flambda
ENV Z3_VERSION    Nightly

ENV HOME /home/opam


ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
    apt-get upgrade -yq && \
    apt-get install -yq aspcud \
                        binutils \
                        cmake curl \
                        g++-8 git \
                        libgmp-dev libgomp1 libomp5 libomp-dev libx11-dev \
                        m4 make \
                        patch python3 python3-distutils \
                        sudo \
                        time tzdata \
                        unzip \
                        vim \
                        && \
    apt-get purge -y gcc g++ && \
    apt-get autoremove -y --purge

RUN update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-8 10 && \
    update-alternatives --install /usr/bin/cc cc /usr/bin/gcc-8 10 && \
    update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-8 10 && \
    update-alternatives --install /usr/bin/c++ c++ /usr/bin/g++-8 10

RUN adduser --disabled-password --home $HOME --shell /bin/bash --gecos '' opam && \
    echo 'opam ALL=(ALL) NOPASSWD:ALL' >>/etc/sudoers && \
    curl -L -o /usr/bin/opam "https://github.com/ocaml/opam/releases/download/$OPAM_VERSION/opam-$OPAM_VERSION-$(uname -m)-$(uname -s)" && \
    chmod 755 /usr/bin/opam && \
    su opam -c "opam init --auto-setup --disable-sandboxing --yes --compiler=$OCAML_VERSION && opam clean"


USER opam
WORKDIR $HOME


RUN opam install --yes alcotest.1.1.0 \
                       core.v0.13.0 \
                       dune.2.5.1 \
                       && \
    opam clean --yes && \
    git clone https://github.com/SaswatPadhi/LoopInvGen.git


WORKDIR $HOME/LoopInvGen


ENV LC_CTYPE=C.UTF-8

RUN curl -LO https://github.com/Z3Prover/z3/archive/$Z3_VERSION.zip && \
    unzip $Z3_VERSION.zip && \
    opam config exec -- ./scripts/build_all.sh --with-logging --build-z3 z3-$Z3_VERSION && \
    rm -rf z3*


ENTRYPOINT [ "opam", "config", "exec", "--" ]
CMD [ "bash" ]