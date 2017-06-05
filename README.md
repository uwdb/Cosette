[![Gitter chat](https://badges.gitter.im/gitterHQ/gitter.png)](https://gitter.im/uwdb/Cosette)
[![Build Status](https://travis-ci.org/uwdb/Cosette.svg?branch=master)](https://travis-ci.org/uwdb/Cosette)

Cosette
=======

Cosette is a langague and an automated solver for reasoning SQL equivalences. See the Cosette [website][web] for more details.

This project is in active development. Shoot us a message (cosette@cs.washington.edu) or create an issue if you find  something doesn't work!


### Using Cosette

SQL equivalences are expressed using the Cosette language. Below is an example (Click on the image to try the online demo). 

<div>
<a href="https://demo.cosette.cs.washington.edu/"> <img src="https://github.com/uwdb/Cosette-Website/blob/gh-pages/images/cosette-ui.png" class="img-responsive" alt="image of Cosette web interface"> </a>
</div>


### Running Cosette

If you want to run Cosette locally, [docker][docker] is the best way to install all Cosette dependencies. You can pull and run the auto built docker container by: 

	docker run  --name cosette --entrypoint /bin/bash -ti shumo/cosette-frontend

This will enter the bash of the container. You can enter the `Cosette` folder and call `solver.py` to run the tool locally.

[web]: http://cosette.cs.washington.edu/.
[docker]: https://docs.docker.com/engine/understanding-docker/


### Web Service API

We are building a HTTP API for others to integrate Cosette into their tools (our [demo website](http://demo.cosette.cs.washington.edu) is an example). Stay tuned for details!
