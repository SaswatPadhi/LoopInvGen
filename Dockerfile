# Adapted from https://github.com/akabe/docker-ocaml/blob/master/dockerfiles/ubuntu16.04_ocaml4.06.1/Dockerfile

FROM ubuntu:16.04

LABEL maintainer="padhi@cs.ucla.edu"


ENV OPAM_VERSION  1.2.2
ENV OCAML_VERSION 4.06.1+flambda
ENV Z3_VERSION    4.6.0

ENV TIME_ZONE     'America/Los_Angeles'

ENV HOME /home/opam


RUN apt update && \
    apt upgrade -y && \
    apt install -y aspcud binutils cmake curl g++ git libgmp-dev libgomp1 \
                   libomp5 libomp-dev libx11-dev m4 make patch python2.7  \
                   sudo tzdata unzip

# Bug in Ubuntu Xenial: https://bugs.launchpad.net/ubuntu/+source/tzdata/+bug/1554806
RUN ln -fs /usr/share/zoneinfo/$TIME_ZONE /etc/localtime && \
    dpkg-reconfigure -f noninteractive tzdata

RUN adduser --disabled-password --home $HOME --shell /bin/bash --gecos '' opam && \
    echo 'opam ALL=(ALL) NOPASSWD:ALL' >>/etc/sudoers

RUN curl -L -o /usr/bin/opam "https://github.com/ocaml/opam/releases/download/$OPAM_VERSION/opam-$OPAM_VERSION-$(uname -m)-$(uname -s)" && \
    chmod 755 /usr/bin/opam

RUN su opam -c "opam init -a -y --comp $OCAML_VERSION"

RUN find $HOME/.opam -regex '.*\.\(cmt\|cmti\|annot\|byte\)' -delete && \
    rm -rf $HOME/.opam/archives \
           $HOME/.opam/repo/default/archives \
           $HOME/.opam/$OCAML_VERSION/man \
           $HOME/.opam/$OCAML_VERSION/build

RUN apt autoremove -y --purge && \
    apt autoclean


USER opam
WORKDIR $HOME


RUN opam install alcotest.0.8.3 core.v0.11.0 core_extended.v0.11.0 jbuilder.1.0+beta20

RUN curl -LO https://github.com/Z3Prover/z3/archive/z3-$Z3_VERSION.zip && \
    unzip z3-$Z3_VERSION.zip && mv z3-z3-$Z3_VERSION z3-$Z3_VERSION
RUN git clone https://github.com/SaswatPadhi/LoopInvGen.git LoopInvGen


WORKDIR $HOME/LoopInvGen


RUN cd LoopInvGen && \
    ./build_all.sh --optimize --make-z3 $HOME/z3-$Z3_VERSION


ENTRYPOINT [ "opam", "config", "exec", "--" ]
CMD [ "bash" ]
