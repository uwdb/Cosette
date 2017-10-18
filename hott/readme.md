### Developing Cosette's Coq Runtime

You can also use Docker to start a Cosette development environment console that has
all the right dependencies setup. From the `Cosette` directory, run:

    docker run --name cosette --entrypoint /usr/bin/fish -v $(pwd)/:/Cosette-Dev -ti shumo/cosette-frontend

You can connect your local `emacs` to the development environment with:

    emacs /docker:cosette:/Cosette-Dev/hott/library/UnivalentSemantics.v

If `user` started Docker on a different `machine`, you can connect your local `emacs` to the development environment with:

    emacs "/ssh:user@machine|docker:cosette:/Cosette-Dev/hott/UnivalentSemantics.v

Make sure your emacs has `ProofGeneral` and `docker-tramp` installed, and
`enable-remote-dir-locals` must be set.
