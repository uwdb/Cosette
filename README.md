[![Gitter chat](https://badges.gitter.im/gitterHQ/gitter.png)](https://gitter.im/uwdb/Cosette)

Cosette
=======

Cosette is a langague and an automated solver for reasoning SQL equivalences. See the Cosette [website][web] for more details.

This project is in active development. Shoot us a message (cosette@cs.washington.edu) or create an issue if you find that something doesn't work!


### Using Cosette

Express SQL equivalences in the Cosette language. Below is an example (Click the image to try the online demo). 

<div>
<a href="https://demo.cosette.cs.washington.edu/"> <img src="https://github.com/uwdb/Cosette-Website/blob/gh-pages/images/cosette-ui.png" class="img-responsive" alt="image of Cosette web interface"> </a>
</div>
 
### Running Cosette

If you want to run Cosette locally, [docker][docker] is the best way to install all Cosette dependencies. You can pull and run the auto built docker container by: 

	docker run  --name cosette --entrypoint /bin/bash -ti shumo/cosette-frontend

This will enter the bash of the container. You can enter cosette folder and call `solver.py` to run Cosette program locally.


[web]: http://cosette.cs.washington.edu/.
[docker]: https://docs.docker.com/engine/understanding-docker/
