# Deep nesting - should not stack overflow or hang

defmodule DeepNesting do
  def deep_lists do
    [[[[[[[[[[[[[[[[[[[[1]]]]]]]]]]]]]]]]]]]]
  end

  def deep_calls do
    a(b(c(d(e(f(g(h(i(j(k(l(m(n(o(p(q(r(s(t(1))))))))))))))))))))
  end

  def deep_pipes do
    1 |> a() |> b() |> c() |> d() |> e() |> f() |> g() |> h() |> i() |> j()
  end

  def deep_binary do
    1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12 + 13 + 14 + 15
  end
end
