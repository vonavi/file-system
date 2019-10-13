Require Import Lists.List.

Inductive Name := nat.
Inductive Storage := L | R.     (* Local / Remote *)

Inductive Tree : Set :=
  | file : Name -> Storage -> Tree
  | dir : Name -> list Tree -> Tree.
Definition FileSystem : Set := list Tree.

Fixpoint tmark (m:Storage) (t:Tree) : Tree :=
  match t with
  | file n _ => file n m
  | dir n fs => dir n (map (tmark m) fs)
  end.

Definition fs_mark (m:Storage) (fs:FileSystem) : FileSystem :=
  map (tmark m) fs.
