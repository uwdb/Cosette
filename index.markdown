---
layout: default
title: Cosette
group: "navigation"
id: home
---


<div style="text-align: center; margin-top: 10px;">
  <a class="github-button" href="https://github.com/uwdb/cosette" data-icon="octicon-star" data-show-count="true" aria-label="Star uwdb/cosette on GitHub">Star</a>
  <a class="github-button" href="https://github.com/uwdb/cosette/fork" data-icon="octicon-repo-forked" aria-label="Fork uwdb/cosette on GitHub">Fork</a>
  <a class="github-button" href="https://github.com/uwdb/cosette/issues" data-icon="octicon-issue-opened" aria-label="Issue uwdb/cosette on GitHub">Issue</a>
</div>

Cosette is an automated prover for checking equivalences of SQL queries. It formalizes a substantial fragment of SQL in the Coq Proof Assistant and the Rosette symbolic virtual machine. It returns either a formal proof of equivalance or a counterexample for a pair of given queries. 

<div class="boxed" align="center">
<font color="red">We will release Cosette in next few weeks.<br>
Stay tuned and sign up on our <a href="https://mailman.cs.washington.edu/mailman/listinfo/cosette">mailing list</a></font>!  
</div>

### Checking SQL Equivalences in Cosette

You can try the Cosette [demo](http://demo.cosette.cs.washington.edu) online, or download its [source code](https://github.com/uwdb/Cosette) from github.

<div>
	<a href='http://demo.cosette.cs.washington.edu'><img src="{{ site.baseurl}}/images/cosette-ui.png" class="img-responsive" alt="Screenshot of the cosette web UI"></a>
	<center><p class="text-center text-muted">Cosette Web UI (click image above to visit demo website)</p></center>
</div>

### How does Cosette work?

Cosette compiles input queries to constraints over symbolic relations and calls [Rosette](http://emina.github.io/rosette/) to find counterexamples, which are input tables that the two input queries return different answer. Cosette also compiles input queries into expressions of K-relations, *UniNomials* we call, which are mathematical functions that returns multiplicity of tuples, using Coq with [Homotopy Type Theory](https://homotopytypetheory.org/). Cosette then tries to search a Coq proof of equivalence of the two input queries given *any* valid input data. The architecture of Cosette is shown as below:

<div>
  <center><img src="{{ site.baseurl}}/images/cosette-arch.png" id="cosettearch" alt="Cosette Architecture"></center>
  <center><p class="text-center text-muted">Cosette System Architecture</p></center>
</div>

### Publications
*  Demonstration of the Cosette Automated SQL Prover. \[ [paper](https://github.com/stechu/stechu.github.io/raw/master/papers/cosette-demo.pdf) \] *SIGMOD 2017 <span style="color:red">(best demo award)</span>*
*  Cosette: An Automated Prover For SQL. \[ [paper](http://cidrdb.org/cidr2017/papers/p51-chu-cidr17.pdf) \]  *CIDR 2017*.
*  HoTTSQL: Proving Query Rewrites with Univalent SQL Semantics. \[ [paper](https://homes.cs.washington.edu/~chushumo/files/cosette_pldi17.pdf) \] \[ [full version](https://homes.cs.washington.edu/~chushumo/files/cosette_pldi_full.pdf) \] \[ [artifact](http://cosette.cs.washington.edu) \]  *PLDI 2017*.
* [Blog Post](https://homotopytypetheory.org/2016/09/26/hottsql-proving-query-rewrites-with-univalent-sql-semantics) on the Homotopy Type Theory Blog.

### Contact

If you have any questions, want to contribute to the project, or just want to say hi, email us at 
[cosette@cs.washington.edu](mailto:cosette@cs.washington.edu). 

### People

Cosette is developed by the [Database Group](http://db.cs.washington.edu/) and the [Programming Languages and Software Engineering Group](http://uwplse.org/) at the [University of Washington](http://www.washington.edu/), the main contributors are:

<a class="person" href="http://shumochu.com/">
  <span class="name">Shumo Chu</span><br/>
  <img class="profile" src="http://stechu.github.io/images/my_portrait.jpg"/>
</a>

<a class="person" href="http://konne.me">
  <span class="name">Konstantin Weitz</span><br/>
  <img class="profile" src="http://www.konne.me/assets/profile.png"/>
</a>

<a class="person" href="http://www.chenglongwang.org">
  <span class="name">Chenglong Wang</span><br/>
  <img class="profile" src="{{ site.baseurl}}/images/chenglong.jpg"/>
</a>

<a class="person" href="https://www.linkedin.com/in/daniel-li-49729a77/">
  <span class="name">Daniel Li</span><br/>
  <img class="profile" src="{{ site.baseurl}}/images/daniel.jpg"/>
</a>

<a class="person" href="https://homes.cs.washington.edu/~akcheung/">
  <span class="name">Alvin Cheung</span><br/>
  <img class="profile" src="https://homes.cs.washington.edu/~akcheung/self.jpg"/>
</a>

<a class="person" href="https://homes.cs.washington.edu/~suciu/">
  <span class="name">Dan Suciu</span><br/>
  <img class="profile" src="https://homes.cs.washington.edu/~suciu/files/me-7-2006-mexico.jpg"/>
</a>

