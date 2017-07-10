---
layout: plain
title: Guide
group: "navigation"
id: guide
---

# The Cosette Guide

by [Shumo Chu](www.shumochu.com)

This document is an introduction to checking SQL equivalences of Cosette, and how to use Cosette web API to build your own tool. 

## Table of Contents
* [The Cosette Language](#lang)
* [SQL Features Covered](#sql)
* [Cosette Web API](#api)

## 1. The Cosette Language <a id="lang"></a>

The get a flavor of the Cosette language, Let's start with a simple Cosette program: 

<pre><code>schema s1(x:int, y:int, ??);

table a(s1);                   -- table a of schema s1

query q1                       -- query 1
`select (x.x + x.x) as ax
 from a x where x.x = x.y`;

query q2                       -- query 2
`select (x.x + x.y) as ax
 from a x where x.x = x.y`;

verify q1 q2;                  -- verify the equivalence
</code></pre>

### 2.1 Schema 

A schema can be declared with a set of attribute names and their data types. In addition to known attributes, `??` can be used to indicate that there could be more attributes in the declared schema, then Cosette will reason about the equivalence assuming that the declared schema has known attributes but could have potentially more attributes. For example, 

<pre><code> schema s1(x:int, y:int, ??); </code></pre> 

Here `s1` can contain any number of attributes, but it has to at least contain integer attributes `x` and `y`. 

### 2.2 Table

A table can be declared with its schema. Such as 

<pre><code> table a(s1); </code></pre> 

declares a table with schema s1. Two tables could have the same schema. 

### 2.3 Query

After declaring schemas and tables, now you can write queries to be checked. Query is declared in a SQL like syntax. Within the Query, you can use tables and attributes (in their schema) declared before as well as integer literals such as `42`. Below is an example of query:

<pre><code> query q1
`select (x.x + x.x) as ax
 from a x where x.x = x.y`;</code></pre> 

Cosette's SQL syntax are more restricted than SQL. These restrictions are helpful to precisely express the SQL semantics:

1. In `select` clause, each field is required to be in the form of `<select-expression> as <field-alias>` such as `(x.x + x.x) as ax`.
2. In `from` clause, each table or subquery is required to be in the form of `<table-or-subquery> <table-alias>` such as `a x`.
3. The reference to an attribute is required in the form of `<table-alias>.<attribute-name>` such as `x.x`.

Cosette supports a substantial fraction of, but not all SQL features ([detailed list](#sql)). If a SQL feature is important to you but not currently supported in Cosette, don't hesitate to submit a [GitHub issue](https://github.com/uwdb/Cosette/issues).

### 2.4 Symbolic Predicate

To reason the equivalences of templated SQL queries, Cosette support symbolic predicate in addition to concrete predicate (e.g. `a.x = 1` is a concrete predicate). Below is a Cosette program with symbolic predicates.

<pre><code>schema s(??);

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

In line 5 and line 6, we defined two symbolic predicates `b1` and `b2`. Symbolic predicates represent any possible predicate that can be applied to a tuple with certain schema. Here, we define `b1` and `b2` on schema `s`. When using symbolic predicate in queries to be checked, a table alias where this predicate is applied is needed. The table alias indicating where the symbolic predicate is applied should have the same schema as the declared one. In `q1`, both `b1` and `b2` are applied to tuples from a table with alias `x`, thus `b1(x)` and `b2(x)`. 
In `q2`, `b1` is applied to tuples from a table with alias `x` and `b2` is applied to tuples from a table with alias `y`.

### 2.5 Verify

Verify statement calls the solver to check the equivalences of the two SQL queries. 

## 2. SQL Features Covered <a id="sql"> </a>

* `SELECT-FROM-WHERE` queries
* `DISTINCT` queries
* `UNION ALL`
* `GROUP BY` (one or more attributes, currently we don't support expressions in GROUP BY yet)
* `=` predicate, `>` and `<` predicate
*  `AND`, `OR`, and `NOT` in predicate
* Aggregate (`SUM`, `COUNT`)
* Correlated (`EXISTS`) and Non-Correlated Subqueries (Subqueries in `FROM` clause). 

## 3. Cosette Web API <a id="api"> </a>

## Contact

If you have any question, want to contribute to the project, email us at 
[cosette@cs.washington.edu](mailto:cosette@cs.washington.edu). 

