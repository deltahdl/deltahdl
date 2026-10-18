#pragma once

#include <optional>
#include <unordered_map>
#include <vector>

#include "common/packed_range.h"

namespace delta {

struct VpiAttachBuild;
struct VpiObject;

// §37.25 detail 10: one dimension of a type as a typespec's ranges draw it,
// unpacked or packed: the bounds of a fixed one, none for a dynamic, queue or
// associative one, whose range is empty (§37.22); the kind of array an
// unpacked one makes, which vpiArrayType reports; and the typespec of an
// associative one's index type, which vpiIndexTypespec reaches (detail 2),
// null for the wildcard index.
struct VpiTypespecDim {
  bool unpacked = false;
  std::optional<PackedRange> bounds;
  int array_type = 0;
  VpiObject* index_typespec = nullptr;
};

// §37.25 detail 8: the typespecs of types written as dimensions over another
// type, each kept with the dimensions it was written with, so that a type
// written over one of them ranges over its dimensions too and unwinds to it.
class VpiTypespecShapes {
 public:
  explicit VpiTypespecShapes(const VpiAttachBuild& build) : build_(build) {}

  // Gives `typespec` the dimensions `dims`, outermost first and at least one,
  // over the typespec `base`: the kind they make, an array typespec where the
  // outermost is unpacked, a bit or logic typespec where the packed ones are
  // over one, and a packed array typespec over anything else; a range per
  // dimension of the outermost one's kind, through `base` where all of
  // `dims` are of it (detail 10), the leftmost one's bounds (detail 9); and
  // the typespec with the outermost dimension removed, `base` itself where
  // none other remains, which vpiElemTypespec reaches.
  void Shape(VpiObject* typespec, const std::vector<VpiTypespecDim>& dims,
             VpiObject* base);

  // An unnamed typespec of `dims` over `base`, hung from `parent`; `base`
  // itself where `dims` is empty.
  VpiObject* Unnamed(VpiObject* parent, const std::vector<VpiTypespecDim>& dims,
                     VpiObject* base);

  // §37.25 detail 6: gives `alias`, the typespec of a typedef standing for the
  // type `aliased` is the typespec of, what that one has: its ranges, its
  // bounds and kind of array, its element or base, its enum consts and its
  // typespec members.
  void Share(VpiObject* alias, VpiObject* aliased);

 private:
  // The dimensions a typespec was written with, over the typespec `base`.
  struct Written {
    std::vector<VpiTypespecDim> dims;
    VpiObject* base = nullptr;
  };

  // The dimensions the ranges of a typespec written as `written` stand for.
  std::vector<const VpiTypespecDim*> Ranged(const Written& written) const;

  std::unordered_map<const VpiObject*, Written> written_;
  const VpiAttachBuild& build_;
};

}  // namespace delta
