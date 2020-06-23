---
title: Logical Foundations - Proof by Induction
category: Teach Yourself
tags: Software Foundations
abbrlink: c03d8d45
date: 2020-06-21 23:59:38
---

> https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html

<!-- more -->

## Proof by Induction

数学归纳法

### 右零元

- $n = 0$
- $n = n' \rightarrow n = S n'$

``` coq
Theorem plus_n_O : ∀n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.
```

## Proofs Within Proofs

`assert`: state and prove the needed "sub-theorem" right at the point where it is used.

``` coq
Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.
```

## Formal vs. Informal Proof

好好写注释

``` coq
Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.   Qed.
```
