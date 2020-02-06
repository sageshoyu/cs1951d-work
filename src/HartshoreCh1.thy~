theory Geometry1_30Start imports Main begin

locale affine_plane_syntax =
  fixes Points :: "'a set" and Lines :: "'a set set"
begin

definition parallel (infix "||" 50)
  where "\<lbrakk> l \<in> Lines; m \<in> Lines \<rbrakk> \<Longrightarrow> l || m \<longleftrightarrow> l = m \<or> \<not> (\<exists> P \<in> Points. P \<in> l \<and> P \<in> m)"
end

definition collinear
  where "\<lbrakk>P \<in> Points; Q \<in> Points; R \<in> Points\<rbrakk> \<Longrightarrow> collinear P Q R \<longleftrightarrow> 
(\<exists>l. P \<in> l \<and> Q \<in> l \<and> R \<in> l)"

locale affine_plane = affine_plane_syntax +
  assumes 
a1: "\<lbrakk>P \<in> Points; Q \<in> Points; P \<noteq> Q \<rbrakk> \<Longrightarrow> \<exists>!l \<in> Lines. P \<in> l \<and> Q \<in> l" and
a2: "\<lbrakk>l \<in> Lines; P \<in> Points; P \<notin> l \<rbrakk> \<Longrightarrow> \<exists>!m \<in> Lines. l || m \<and> P \<in> m" and
a3: "\<exists> P Q R . (P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> Q \<noteq> R) \<and> 
\<not> (\<exists>m \<in> Lines. P \<in> m \<and> Q \<in> m \<and> R\<in>m)"
begin

(* work on affine planes to take place here *)
(* perhaps define collinear? *)

(* try to prove, for instance, that if k and m are distinct, then they intersect in at 
most one point *)
(* NB: The axioms above are DELIBERATELY incorrect as stated. Let's try to fix them. *)

theorem collinear_comm: "\<lbrakk>A \<in> Points; B \<in> Points; C \<in> Points; collinear A B C\<rbrakk> \<Longrightarrow> collinear A C B"
  using collinear_def by fastforce

lemma parallel_symm[simp]: "\<lbrakk>l \<in> Lines; m \<in> Lines; l || m\<rbrakk> \<Longrightarrow> m || l"
  using parallel_def by blast

lemma parallel_refl[simp]: "\<lbrakk>l \<in> Lines\<rbrakk> \<Longrightarrow> l || l"
  using parallel_def by blast

lemma parallel_trans[simp]: "\<lbrakk>l \<in> Lines; m \<in> Lines; n \<in> Lines; l || m; m || n\<rbrakk> \<Longrightarrow> l || n"
  by (metis a2 parallel_def)

(* Every point lies on some line *)
lemma line_for_point: "\<lbrakk>P \<in> Points\<rbrakk> \<Longrightarrow> \<exists>l \<in> Lines . P \<in> l"
  by (metis a1 a3)

lemma no_empty_line: "{} \<notin> Lines"
proof - 
  have "{} \<in> Lines \<Longrightarrow> False"
  proof -
    obtain P Q R where PQR: "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> Q \<noteq> R \<and> 
\<not> (\<exists>m \<in> Lines. P \<in> m \<and> Q \<in> m \<and> R\<in>m)" using a3 by blast
    obtain PQ where PQ: "PQ \<in> Lines \<and> P \<in> PQ \<and> Q \<in> PQ"
      using a1 PQR by metis
    obtain PR where PR: "PR \<in> Lines \<and> P \<in> PR \<and> R \<in> PR"
      using a1 PQR by metis
    have "PQ || {} \<and> PR || {}" try
  qed
qed

(* Every line contains at least one point *)
lemma contained_point: "\<lbrakk>l \<in> Lines\<rbrakk> \<Longrightarrow> \<exists>P \<in> Points . P \<in> l"
  try

(* Every line contains at least two points *)
lemma contains_two_points: "\<lbrakk>l \<in> Lines\<rbrakk> \<Longrightarrow> \<exists> P Q . P \<in> Points \<and> Q \<in> Points 
\<and> P \<in> l \<and> Q \<in> l \<and> P \<noteq> Q"
  sorry

lemma contains_three_points:  "\<lbrakk>l \<in> Lines\<rbrakk> \<Longrightarrow> \<exists> P Q R . (P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points 
\<and> P \<in> l \<and> Q \<in> l \<and> R \<in> l \<and> P \<noteq> Q \<and> Q \<noteq> R)"
  try

end (* affine_plane locale *)

end (* theory *)
