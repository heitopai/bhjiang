---
title: Lean4极简导读
date: 2025-11-05
math: true
---
Lean是一种开源**编程语言**（lean4的4是版本，也有lean3等），
能用来形式化数学，用代码来表达数学命题和证明，以方便验证证明是否正确，官网 https://lean-lang.org/

例子：
```
/-- A prime is a number larger than 1 with no trivial divisors -/
def IsPrime (n : Nat) := 1 < n ∧ ∀ k, 1 < k → k < n → ¬ k ∣ n

/-- Every number larger than 1 has a prime factor -/
theorem exists_prime_factor :
    ∀ n, 1 < n → ∃ k, IsPrime k ∧ k ∣ n := by
  intro n h1
  -- Either `n` is prime...
  by_cases hprime : IsPrime n
  · grind [Nat.dvd_refl]
  -- ... or it has a non-trivial divisor with a prime factor
  · obtain ⟨k, _⟩ : ∃ k, 1 < k ∧ k < n ∧ k ∣ n := by
      simp_all [IsPrime]
    obtain ⟨p, _, _⟩ := exists_prime_factor k (by grind)
    grind [Nat.dvd_trans]
```

上述lean4代码说了这样一件事：
- def 定义了什么是素数, ∧ ∀ → ¬这些符号都和数学的通常的含义一样
- theorem 定理的名字是exists_prime_factor，这个定理证明了每个大于1的自然数都有一个素因子。by后面的是证明过程，intro，by_cases，grind，obtain这些叫做Tactic，叫什么不重要，intro的意思大概是引入固定的n，h1是n满足1 < n这一事实，我们用自然语言证明这个结论也要类似的说对于给定n>1，所以很类似。其他的，不说了，这里是极简导读

上述代码可以直接在 https://live.lean-lang.org/ 运行，显示No goals以及No messages就说明证明没问题。点击代码的不同位置可以看到右侧的不同信息，可以体验一下，具体什么意思下一篇介绍。


## 入门建议

- 我自己就是通过官方的自然数游戏入门 https://adam.math.hhu.de/#/g/leanprover-community/nng4 
- 文档因人而异看
- 社区的话多逛Mathlib（大型数学定义和定理库）和Lean Community Zulip（答疑，分享等）吧
- 想本地安装lean4的话一般很麻烦