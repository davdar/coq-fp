Require Import FP.Categories.
Require Import FP.CoreData.
Require Import FP.Data.Type.

Import CategoriesNotation.

Definition sequence_fst {t A B} `{! FUnit t ,! FApply t } (p:t A*B)  : t (A*B) :=
  let (aT,b) := p in funit pair <@> aT <@> funit b.

Definition sequence_snd {t A B} `{! FUnit t ,! FApply t } (p:A*t B)  : t (A*B) :=
  let (a,bT) := p in funit pair <@> funit a <@> bT.
