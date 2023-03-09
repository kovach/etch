# syntax=docker/dockerfile:1
#FROM ubuntu:18.04
FROM python
RUN apt-get update && apt-get install -y \
  curl \
  #python \
  #python-pip \
  sqlite3

#RUN apt-get install -y python3 python3-pip

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
RUN python -m pip install --user pipx
RUN python -m pipx ensurepath
RUN . ~/.profile
#RUN pipx install mathlibtools
RUN pip install mathlibtools
COPY . .

ENV PATH "/root/.elan/bin:${PATH}"
# return with no error -> no incomplete proofs
RUN leanproject build

WORKDIR "/etch4"
RUN elan self update
RUN lake update
RUN lake exe cache get
#RUN lake build
RUN lake exe bench
RUN make
