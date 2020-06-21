---
title: Logical Foundations - Proof by Simplification
category: Teach Yourself
tags: Software Foundations
abbrlink: f89f2075
date: 2020-06-21 21:18:19
---

> https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html#lab33

<!-- more -->

## 证明左零元

``` coq
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.  Qed.
```

- `simpl`并不是必要的，`reflexivity`在判断相等时会做一些化简的工作
- `Example`, `Theorem`, `Lemma`, `Fact` and `Remark`是一样的，只是风格不同
- `intros n`把题设中的$\forall n: nat$引入到证明的上下文里来
- `intros`, `simpl`, and `reflexivity`都是预设的策略，用于在`Proof`和`Qed`之间指导证明的运行（类似于指令）

``` coq
Theorem plus_1_l : ∀n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : ∀n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.
```

