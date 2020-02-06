theory PnP_Exercises imports Main
begin
(* 2.1 *)
value "1+(2::nat)"
value "1+(2::int)"
value "1-(2::nat)"
value "1-(2::int)"

(* 2.2 *)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" | 
"add (Suc m) n = Suc(add m n)"

lemma add_02[simp]: "add m 0 = m"
  apply(induction m)
  apply(auto)
  done

theorem add_assoc: "add (add x y) z = add x (add y z)"
  apply (induction x)
  apply (auto)
  done

lemma add_03: "m = add m 0"
  apply simp
  done

lemma add_05[simp]: "add 0 m = add m 0"
  apply (simp)
  done 

lemma add_06[simp]: "Suc(add x y) = add x (Suc y)"
  apply (induction x)
  apply (auto)
  done
lemma add_07[simp]: "add x (Suc y) = Suc (add x y)"
  apply (simp)
  done

theorem add_comm: "add x y = add y x"
  apply (induct x)
  apply (simp)
  using add.simps(2) add_07 by presburger


fun double :: "nat \<Rightarrow> nat" where 
"double 0 = 0" | 
"double (Suc n) = Suc(Suc(double n))"

lemma double_2: "double 0 = add 0 0"
  apply (simp)
  done

theorem double_add: "double n = add n n"
  apply (induction n)
  apply (simp)
  using add.simps(2) add_06 double.simps(2) by presburger

(* 2.3 *)
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x [] = 0" |
"count x (Cons y xs) = (count x xs) + (if x = y then 1 else 0)"

theorem count_lt_len: "count x y \<le> length y"
  apply (induction y)
  apply (simp)
  apply (auto)
  done
end

