# syntax=docker/dockerfile:1
FROM python
RUN apt-get update && apt-get install -y \
  curl \
  sqlite3

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
RUN python -m pip install --user pipx
RUN python -m pipx ensurepath
RUN . ~/.profile
#RUN pipx install mathlibtools
RUN pip install mathlibtools
RUN python -m pip install --user numpy matplotlib
RUN apt-get install -y clang lldb vim

COPY . .

ENV PATH "/root/.elan/bin:${PATH}"

# STEP 1: return with no error -> no incomplete proofs
RUN leanproject build

WORKDIR "/etch4"
RUN elan self update
RUN lake update
# compile and run ETCH to generate C code
RUN lake exe bench
# compile generated code
RUN make out wcoj

# STEP 2: generate wcoj scaling figure `wcoj_scalaing.pdf`
RUN python run_wcoj_trials.py
# STEP 3: invoke compiled code to print human readable numbers for graphs. see stdout for details
RUN "./out"
