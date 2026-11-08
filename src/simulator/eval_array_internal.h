#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"

namespace delta {

struct ArrayInfo;
struct AssocArrayObject;
struct Expr;
struct QueueObject;
class SimContext;
class Arena;

std::vector<Logic4Vec> CollectVecElements(std::string_view var_name,
                                          const ArrayInfo& info,
                                          SimContext& ctx, Arena& arena);

void CollectAssocKeyVals(const AssocArrayObject& aa, Arena& arena,
                         std::vector<Logic4Vec>& keys,
                         std::vector<Logic4Vec>& vals);

bool IsStringArray(std::string_view var_name, const ArrayInfo& info,
                   SimContext& ctx);

struct IterNames {
  std::string_view iter_name;
  std::string_view index_name;
  std::string idx_var_name;
};

IterNames ExtractIterNames(const Expr* expr);

class IteratorLayout {
 public:
  IteratorLayout(std::string_view iter_name, std::string_view array_name,
                 SimContext& ctx);
  ~IteratorLayout();
  IteratorLayout(const IteratorLayout&) = delete;
  IteratorLayout& operator=(const IteratorLayout&) = delete;

 private:
  SimContext& ctx_;
  std::string_view iter_name_;
  std::string_view previous_;
  bool bound_ = false;
};

bool HasSubarrayElements(const ArrayInfo& info);

struct SubarrayElement {
  std::string_view array_name;
  const ArrayInfo& info;
  uint32_t offset;
};

void BindSubarrayIterator(const SubarrayElement& element,
                          std::string_view iter_name, SimContext& ctx,
                          Arena& arena);

bool ResolveSubarraySelect(const Expr* sel, SimContext& ctx, Arena& arena,
                           std::string& prefix, ArrayInfo& sub);

std::optional<Logic4Vec> TryAssocReduction(AssocArrayObject* aa,
                                           std::string_view method,
                                           const Expr* expr, SimContext& ctx,
                                           Arena& arena);

uint64_t ApplyReduction(std::string_view method,
                        const std::vector<uint64_t>& vals);

bool OrdersBefore(const Logic4Vec& a, const Logic4Vec& b, bool is_signed);

void SortQueueByWithExpr(QueueObject* q, const Expr* expr, bool ascending,
                         SimContext& ctx, Arena& arena);

}  // namespace delta
