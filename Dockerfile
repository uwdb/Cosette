FROM ubuntu:14.04.2
MAINTAINER Konstantin Weitz <konstantin.weitz@gmail.com>

RUN apt-get update && \
    apt-get install -y \
      binutils \
      camlp5 \
      curl \
      git \
      g++ \
      libpcre3-dev \
      libpcre-ocaml-dev \
      make \
      software-properties-common \
      vim \
      wget \
      fish

RUN git clone https://github.com/HoTT/HoTT.git && \
    cd HoTT && \
    git checkout 93cedccd3c31fe3bb2d774c9acedd2d0923dc958 && \
    etc/install_coq.sh && \
    ./autogen.sh && \
    ./configure COQBIN="`pwd`/coq-HoTT/bin" && \
    make -j `nproc` && \
    make install

RUN curl -O https://coq.inria.fr/distrib/V8.5pl1/files/coq-8.5pl1.tar.gz && \
    tar -xvf coq-8.5pl1.tar.gz && \
    cd coq-8.5pl1; ./configure \
                       -bindir /usr/local/bin \
                       -libdir /usr/local/lib/coq \
                       -configdir /etc/xdg/coq \
                       -datadir /usr/local/share/coq \
                       -mandir /usr/local/share/man \
                       -docdir /usr/local/share/doc/coq \
                       -emacs /usr/local/share/emacs/site-lisp \
                       -coqdocdir /usr/local/share/texmf/tex/latex/misc && \
                     make -j `nproc` && \ 
                     make install
