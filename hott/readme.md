### Developing Cosette's Coq Runtime

You can also use Docker to start a Cosette development environment console that has
all the right dependencies setup. From the `Cosette` directory, run:

    docker rm -f cosette; docker run 

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
