# DopCert
DopCert is a framework for formally verifying query optimization. 
Our website: http://dopcert.cs.washington.edu/.

Our coq code has been tested with coq 8.5pl1, you need to install [HoTT](https://github.com/HoTT/HoTT) library as well. So we recommend users to use the docker development environment as described below.

## Build Project

Build project and call it `dopcert` with:

    docker build -t dopcert .
 
## Develop Project
 
Run development environment named `dopcert` with:

    docker run -d --name dopcert -v $(pwd)/src/:/src/ dopcert sleep infinity
 
Build changes to the project with:

    docker exec dopcert make -C src

Connect to the docker process with emacs and edit Coq files using ProofGeneral.
Emacs must have `docker-tramp` installed, and `enable-remote-dir-locals` enabled.

    emacs /docker:dopcert:/hott/UnivalentSemantics.v

Remove development environment with:
    
    docker rm -f dopcert

Remove all old docker containers with:

    docker rm -f $(docker ps -aq)
