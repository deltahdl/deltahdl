#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/packed_range.h"

namespace delta {

enum class DataTypeKind : uint8_t;
class SimContext;
struct Expr;
struct VpiAttachBuild;
struct VpiObject;

struct VpiTypespecDim {
  bool unpacked = false;
  std::optional<PackedRange> bounds;
  int array_type = 0;
  VpiObject* index_typespec = nullptr;
};

VpiTypespecDim VpiUnpackedTypespecDim(const Expr* dim, SimContext& ctx);

std::optional<DataTypeKind> VpiAssocIndexKeywordKind(std::string_view written);

class VpiTypespecShapes {
 public:
  explicit VpiTypespecShapes(const VpiAttachBuild& build) : build_(build) {}

  void Shape(VpiObject* typespec, const std::vector<VpiTypespecDim>& dims,
             VpiObject* base);

  VpiObject* Unnamed(VpiObject* parent, const std::vector<VpiTypespecDim>& dims,
                     VpiObject* base);

  void Share(VpiObject* alias, VpiObject* aliased);

 private:
  struct Written {
    std::vector<VpiTypespecDim> dims;
    VpiObject* base = nullptr;
  };

  std::vector<const VpiTypespecDim*> Ranged(const Written& written) const;

  std::unordered_map<const VpiObject*, Written> written_;
  const VpiAttachBuild& build_;
};

}  // namespace delta
