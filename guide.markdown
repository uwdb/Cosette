---
layout: plain
title: Guide
group: "navigation"
id: guide
---

# The Cosette Guide

by [Shumo Chu](www.shumochu.com) and [Alvin Cheung](https://homes.cs.washington.edu/~akcheung/)

This document discusses how Cosette checks equivalence of SQL queries, 
and how to use Cosette web API to build your own tool. 

## Table of Contents
* [The Cosette Language](#lang)
* [SQL Features Covered](#sql)
* [Cosette Web API](#api)

## 1. The Cosette Language <a id="lang"></a>

The get a flavor of the Cosette language, Let's start with a simple Cosette program: 

<pre><code>
schema s1(x:int, y:int, ??);   -- schema declaration

table a(s1);                   -- table a of schema s1

query q1                       -- query 1 on table a
`select (x.x + x.x) as ax
 from a x 
 where x.x = x.y`;

query q2                       -- query 2 on table a
`select (x.x + x.y) as ax
 from a x 
 where x.x = x.y`;

verify q1 q2;                  -- does q1 equal to q2?
</code></pre>

### 2.1 Schema 

To use Cosette, we start by defining a schema for the tables that we will query on.
A schema is declared with a set of attribute names and their data types. In
addition to known attributes, we use `??` to indicate that there could be
more "symbolic" attributes in the declared schema but they aren't used in queries. 
For example, 

<pre><code> schema s1(x:int, y:int, ??); </code></pre> 

Here `s1` can contain any number of attributes, but it has to at least contain integer attributes `x` and `y`. 

If Cosette concludes that two queries with symbolic attributes are equivalent, 
then they are equivalent regardless of what those symbolic attributes are instantiated with.

### 2.2 Table

We next declare tables using the defined schemas. For instance:

<pre><code> table a(s1); </code></pre> 

declares a table with schema `s1`. Multiple tables can have the same schema. 

### 2.3 Query

After declaring schemas and tables, we can now write the queries to be checked.
A Cosette query is written using a SQL-like syntax. Within the Query, we can use tables
and attributes declared earlier as well as integer literals
such as `42`. Here is an example of query:

<pre><code> query q1
`select (x.x + x.x) as ax
 from a x 
 where x.x = x.y`;</code></pre> 

Note the use of \` \` to denote the query itself. 
Cosette's SQL syntax are more restricted (say compared to that of MySQL or T-SQL).
These restrictions are helpful to precisely express query semantics:

1. In the `select` clause, each projected attribute must be named using `<select-expression> as <field-alias>` such as `(x.x + x.x) as ax`.
2. In the `from` clause, each table or subquery is of the form `<table-or-subquery> <table-alias>` such as `a x`.
3. Each attribute reference must be fully qualified with `<table-alias>.<attribute-name>` such as `x.x`.

Currently Cosette supports a substantial fraction of, but not all SQL features
([detailed list](#sql)). If a SQL feature is important to you but not currently
supported in Cosette, don't hesitate to submit a 
[GitHub issue](https://github.com/uwdb/Cosette/issues).

### 2.4 Symbolic Predicates

To reason the equivalences of templated SQL queries, Cosette support symbolic
predicates in addition to concrete predicates (`a.x = 1` is a concrete
predicate). This is similar to symbolic attributes mentioned earlier.
Here is a Cosette program with symbolic predicates:

<pre><code>schema s(??);       -- a schema with arbitrary (symbolic) attributes

table r(s);

predicate b1(s);    -- symbolic predicate b1 on s
predicate b2(s);    -- symbolic predicate b2 on s

query q1
`select distinct * from r x where b1(x) or b2(x)`;

query q2
`select distinct *
 from ((select * from r x where b1(x)) 
       union all (select * from r y where b2(y))) x`;
 
verify q1 q2;
</code></pre> 

In lines 5 and 6, we defined two symbolic predicates `b1` and `b2`. Symbolic
predicates represent *any* predicate that can be applied to a tuple with
the specified schema (schema `s` in `b1` and `b2` above). When using
symbolic predicates in queries, we need to provide which table is the predicate
applied to using table aliases, and the table that the predicate is
applied to should have the same schema as that in the predicate's 
declaration.

For instance, in `q1`, both `b1`
and `b2` are applied to tuples from a table with alias `x`, i.e., `b1(x)` and
`b2(x)`. While in `q2`, `b1` is applied to tuples from a table with alias `x` and
`b2` is applied to tuples from a table with alias `y`.

### 2.5 Verify

Finally, 
the verify statement calls the solver to check the equivalences of the two SQL queries. 
**Alvin: add what is returned**

## 2. SQL Features Covered <a id="sql"> </a>

* `SELECT-FROM-WHERE` queries
* `DISTINCT` queries
* `UNION ALL`
* `GROUP BY` (one or more attributes, currently we don't support expressions in `GROUP BY` yet)
* `=`, `>`, and `<` predicates
*  `AND`, `OR`, and `NOT` predicates
* Aggregates (`SUM`, `COUNT`)
* Correlated queries (`EXISTS`) and non-Correlated Subqueries (Subqueries in `FROM` clause). 

## 3. Cosette Web API <a id="api"> </a>

Cosette provides a web REST API for you to integrate our tool in your application.

### 2.1 Get an API key

1. Register as a user of Cosette Web Service by going to
[Cosette Demo](http://demo.cosette.cs.washington.edu). 
2. After you
finished registration or logged in as a returning user, you will notice a link on
the upper left corner of the demo web page (see below). Click it and get your
API key!

<div>
<a href='http://demo.cosette.cs.washington.edu'><img src="{{ site.baseurl}}/images/api_key.png" class="img-responsive" alt="Screenshot of the cosette API key"></a>
</div>

### 2.2 Cosette Web API

**Request URL**

```POST https://demo.cosette.cs.washington.edu/solve```

*(Note: It is a https URL!).* 

**Request Body**

In the request body, supply data with the following structure:

```JavaScript
{
      "api_key": api_key,     // API key (see 2.1)
      "query": query          // your cosette program
}
```

**Response**

Our web service returns a response body with the following structure:

```JavaScript
{
      "result": result,                   // can be EQ, NEQ, UNKNOWN, or ERROR
      "counterexamples": counterexamples, // counterexample if result is NEQ
      "coq_source": coq_source,           // generated Coq source code
      "rosette_source": rosette_source,   // generated Rosette source code
      "error_msg": error_msg,             // error message if result = ERROR
}

```

**Example Code** 

<ul class="nav nav-tabs" role="tablist">
  <li class="nav-item">
      <a class="nav-link active" data-toggle="tab" role="tab" href="#api_python">Python</a></li>
  <li class="nav-item">
      <a class="nav-link" data-toggle="tab" href="#api_js" role="tab">JavaScript</a>
      </li>
</ul>

<div class="tab-content">
  <div class="tab-pane active" id="api_python" role="tabpanel">
   <p>
      <code>
      <pre>import requests

r = requests.post("https://demo.cosette.cs.washington.edu/solve", 
                  data={"api_key":"[your api key]", "query":"[your cosette program]"})

print r.text</pre>
      </code>
   </p>
  </div>
  <div class="tab-pane" id="api_js" role="tabpanel"> 
  <p> 
      <code>
      <pre> // require jQuery
    $.ajax({
        method: 'POST',
        url: 'https://demo.cosette.cs.washington.edu/solve',
        dataType: 'json',
        data: {
            "api_key": "[your api key]",
            "query": "[your cosette program]",
        },
        success: function(data){
            console.log(data);
        },
        error: function(jqXHR, textStatus, errorThrown){
            console.log(errorThrown);
        }
    });
      </pre>
      </code>
  </p>
  </div>
</div>

You will get a json response, which include the result and other
information. The result is shown in the `result` field and can be `EQ`, `NEQ`,
`UNKNOWN`, or `ERROR`. If the result is `NEQ`, there will be another field named
`counterexamples` that shows the counter examples. If the result is
`ERROR`, then there is another field named "error_msg" indicating the details
of the error. You can look into `rosette_source` and `coq_source` to check the
generated Rosette and Coq code as well. 



## Contact

If you have any questions, comments, want to contribute to the project, email us at 
[cosette@cs.washington.edu](mailto:cosette@cs.washington.edu). 
