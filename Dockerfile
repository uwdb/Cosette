FROM ubuntu:latest

ARG DEBIAN_FRONTEND=noninteractive

####### Install Dependencies #######################
RUN apt-get -y update
RUN apt-get -y install build-essential curl zlib1g-dev libgmp3-dev libedit2 python libpangocairo-1.0-0 libjpeg62

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
      fish \
      python3-pip

############# install racket #######################
RUN wget https://mirror.racket-lang.org/installers/7.9/racket-7.9-x86_64-linux.sh
RUN echo -ne "\n\n" | sh racket-7.9-x86_64-linux.sh

############# add to the path ######################
ENV PATH /usr/racket/bin:$PATH
ENV LANG C.UTF-8

############# install rosette ######################
RUN raco pkg install --batch --auto rosette;

RUN git clone -b minimal-grader https://github.com/uwdb/Cosette.git

RUN pip3 install antlr4-python3-runtime
