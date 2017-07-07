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

After declaring schemas and tables, now you can declar queries to be checked. Query is declared in a SQL like syntax. Within the Query, you can use tables and attributes (in their schema) declared before as well as integer literals such as `42`. Below is an example of query:

<code><pre> query q1
`select (x.x + x.x) as ax
 from a x where x.x = x.y`;</code></pre> 

Cosette's SQL syntax are more restricted than SQL. These restrictions are helpful to precisely express the SQL semantics:
1. In `select` clause, each field is required to be in the form of `<select-expression> as <field-alias>` such as `(x.x + x.x) as ax`.
2. In `from` clause, each table or subquery is required to be in the form of `<table-or-subquery> <table-alias>` such as `a x`.
3. The reference to an attribute is required in the form of `<table-alias>.<attribute-name>` such as `x.x`.

Cosette supports a substantial fraction of, but not all SQL features ([detailed list](#sql)). If a SQL feature is important to you but not currently supported in Cosette, don't hesitate to submit a [GitHub issue](https://github.com/uwdb/Cosette/issues).

### 2.4 Symbolic Predicate

### 2.5 Verify

## 2. SQL Features Covered <a id="sql"> </a>

## 3. Cosette Web API <a id="api"> </a>

## Contact

If you have any question, want to contribute to the project, or just want to say hi, email us at 
[cosette@cs.washington.edu](mailto:cosette@cs.washington.edu). 

