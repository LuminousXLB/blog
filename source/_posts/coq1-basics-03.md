---
title: Logical Foundations - Proof by Rewriting
category: Teach Yourself
tags: Software Foundations
abbrlink: 8f9810e3
date: 2020-06-21 21:42:02
---

> https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html#lab34

<!-- more -->

## 引入条件并使用

``` coq
Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity.  Qed.
```

- The arrow symbol is pronounced "implies."
- 第二行引入条件 `n = m` 并命名为 `H`.
- 第三行rewrite当前的目标：把当前目标中，`H`的左边替换`H`的右边（即按照从左到右的方向应用`H`到当前的目标上）

## 使用已经证明的定理

``` coq
Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.
```
