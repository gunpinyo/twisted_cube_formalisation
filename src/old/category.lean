universes u v

structure category :=
  (obj   : Type u)
  (hom   : obj → obj → Type v)
  (id    : Π (X : obj), hom X X)
  (comp  : Π {X Y Z : obj}, hom X Y → hom Y Z → hom X Z)
  (id_l  : ∀ {X Y : obj} (f : hom X Y), comp (id X) f = f)
  (id_r  : ∀ {X Y : obj} (f : hom X Y), comp f (id Y) = f)
  (assoc : ∀ {X Y Z W : obj} (f : hom X Y) (g : hom Y Z) (h : hom Z W),
             comp (comp f g) h = comp f (comp g h))

namespace category
  structure iso (C : category) (X Y : C.obj) :=
    (dir     : C.hom X Y)
    (inv     : C.hom Y X)
    (dir_inv : C.comp dir inv = C.id X)
    (inv_dir : C.comp inv dir = C.id Y)
end category
