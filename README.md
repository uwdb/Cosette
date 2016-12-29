Cosette
=======

Cosette is an automated SQL solver. See the Cosette [website][web] for more details.

This repository contains Cosette's Coq code. We will release the Rosette code later.


### Running Cosette

[Docker][docker] is the most reliable way to get Cosette running. To download a compiled version of Cosette and all its dependencies run (running this command for the first time may take a while):

     docker pull konne/cosette
     
You can test that Cosette works correctly by running an example application that TODO:

    docker run konne/cosette TODO
 
### Building Cosette

To locally build Cosette and all its dependencies using Docker, run (running this command for the first
time may take over an hour):

    git clone git@github.com:uwdb/Cosette.git
    cd Cosette
    docker build -t konne/cosette .

Once built, Cosette can be run just like the downloaded and compiled version of Cosette with `dcoker run konne/cosette`.

If you prefer to build Cosette without Docker, you must install the [HoTT](https://github.com/HoTT/HoTT) library with Coq 8.5pl1. For more precise instructions, consult the `Dockerfile`.

### Developing Cosette

You can also use Docker to start a Cosette development environment console that has
all the right dependencies setup. From the `Cosette` directory, run:

    docker rm -f cosette; docker run --name cosette --entrypoint /bin/bash -v $(pwd)/hott:/hott -ti konne/cosette

Alternatively, if you like the `fish` shell (i do) run:

    docker rm -f cosette; docker run --name cosette --entrypoint /usr/bin/fish -v (pwd)/hott:/hott -ti konne/cosette

The `-v $(pwd)/hott:/hott` argument mounts the `Cosette/hott` directory inside the Docker development environment at `/hott`, so any changes to files within `/hott` will be preserved even after the Docker development environment is stopped.

You can now build the project in development environment console with:

    make -C /hott

You can connect your local `emacs` to the development environment with:

    emacs /docker:cosette:/hott/UnivalentSemantics.v

If `user` started Docker on a different `machine`, you can connect your local `emacs` to the development environment with:

    emacs "/ssh:user@machine|docker:cosette:/hott/UnivalentSemantics.v

Make sure your emacs has `ProofGeneral` and `docker-tramp` installed, and
`enable-remote-dir-locals` must be set.


[web]: http://cosette.cs.washington.edu/.
[docker]: https://docs.docker.com/engine/understanding-docker/
