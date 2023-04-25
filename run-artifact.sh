set -e
# build the docker image
docker build -t etch-bench -f graphs/Dockerfile .
# perform benchmarks. may take 1-2 hours
docker run --rm -v '.:/mnt' -e HOME=/mnt -w /mnt -u $(id -u):$(id -g) etch-bench bash graphs/run.sh
# generate figures
docker run --rm -v '.:/mnt' -e HOME=/mnt -w /mnt -u $(id -u):$(id -g) etch-bench python3 graphs/graph.py
