#pragma once

#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "parser/ast_type.h"

namespace delta {

struct Expr;

struct SelfType {
  uint32_t width = 0;
  bool is_signed = false;
  bool four_state = false;
  bool known = false;
};

struct TypenameEnvironment {
  std::function<int64_t(const Expr*)> value_of;
  std::function<const DataType*(std::string_view, std::string_view,
                                std::string&)>
      resolve_name;
  std::function<std::string(std::string_view, std::string_view)>
      qualified_class_name;
  std::function<std::string_view()> scope_name;
  std::function<uint32_t(const DataType&)> width_of;
  std::function<SelfType(std::string_view)> name_self_type;
  std::function<bool(const Expr*)> is_real;
  std::function<uint32_t(std::string_view)> element_width;
};

struct TypenameParts;

class TypenameWriter {
 public:
  explicit TypenameWriter(const TypenameEnvironment& env) : env_(env) {}

  std::string OfType(const DataType& type, std::string_view scope,
                     std::string_view hint);

  std::string OfMember(const StructMember& member, std::string_view scope);

 private:
  std::string PackedText(const TypenameParts& parts);
  std::string RangeText(const Expr* left, const Expr* right);
  std::string OfParts(const TypenameParts& parts, std::string_view scope,
                      std::string_view hint);
  std::string OfName(const TypenameParts& parts, std::string_view scope);
  std::string OfUnresolvedName(const TypenameParts& parts,
                               const std::string& prefix);
  std::string TypeOwnerPrefix(std::string_view prefix);
  std::string Anonymous(const DataType& type, std::string_view scope,
                        std::string_view hint);
  std::string OfStructUnionOrEnum(const DataType& type,
                                  const std::string& name);
  std::string OfEnum(const DataType& type);

  const TypenameEnvironment& env_;
};

std::optional<DataType> KeywordTypeOf(const Expr* arg);

std::string UnpackedDimsText(const RtlirVariable& var);

std::string ElementDimsText(std::string_view unpacked);

std::string TypenameOfOperation(const Expr* arg,
                                const TypenameEnvironment& env);

}  // namespace delta
