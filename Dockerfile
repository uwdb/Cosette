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

RUN apt-get update && \
    apt-get install -y automake 

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

####### Install Dependencies ###################################################
RUN apt-get -y update
RUN apt-get -y install build-essential curl zlib1g-dev libgmp3-dev libedit2

############## install haskell #####################
RUN curl -O http://downloads.haskell.org/~ghc/8.0.2/ghc-8.0.2-x86_64-deb7-linux.tar.xz
RUN tar xvfJ ghc-8.0.2-x86_64-deb7-linux.tar.xz
RUN cd ghc-8.0.2 && ./configure
RUN cd ghc-8.0.2 && make install

############# install cabal ########################
RUN curl -O http://hackage.haskell.org/package/cabal-install-1.24.0.2/cabal-install-1.24.0.2.tar.gz
RUN tar xvfz cabal-install-1.24.0.2.tar.gz
RUN cd cabal-install-1.24.0.2 && sh ./bootstrap.sh
ENV PATH /root/.cabal/bin/:$PATH
ENV LANG C.UTF-8

RUN git clone -b pldi-ae https://github.com/uwdb/Cosette.git

RUN cd /Cosette/dsl && cabal sandbox init
RUN cabal update
RUN cd /Cosette/dsl && cabal install Parsec
RUN cd /Cosette/dsl && ghc CoqCodeGen.lhs

# ADD hott /hott
# RUN make -C /hott
