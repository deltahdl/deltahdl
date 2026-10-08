#include "simulator/struct_string_member.h"

#include <cstdint>
#include <string>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"

namespace delta {

namespace {

// Every text a handle names, by handle, and the handle of each text; the
// empty string is handle 0.
struct StringMemberTable {
  std::vector<std::string> texts{""};
  std::unordered_map<std::string, uint64_t> handles{{"", 0}};
};

StringMemberTable& Table() {
  static StringMemberTable table;
  return table;
}

}  // namespace

Logic4Vec StringMemberHandle(const Logic4Vec& text, Arena& arena) {
  StringMemberTable& table = Table();
  auto [it, inserted] =
      table.handles.try_emplace(Logic4VecToString(text), table.texts.size());
  if (inserted) table.texts.push_back(it->first);
  return MakeLogic4VecVal(arena, kStringMemberHandleWidth, it->second);
}

Logic4Vec StringMemberText(const Logic4Vec& handle, Arena& arena) {
  // §11.9: a structure a read inconsistent with a tagged union's tag gave all
  // x holds an x handle, which names the empty string.
  uint64_t index = handle.IsKnown() ? handle.ToUint64() : 0;
  Logic4Vec text = StringToLogic4Vec(arena, Table().texts[index]);
  text.is_string = true;
  return text;
}

Logic4Vec MemberBitsOf(const Logic4Vec& val, DataTypeKind kind, Arena& arena) {
  return kind == DataTypeKind::kString ? StringMemberHandle(val, arena) : val;
}

Logic4Vec MemberValueOf(const Logic4Vec& bits, DataTypeKind kind,
                        Arena& arena) {
  return kind == DataTypeKind::kString ? StringMemberText(bits, arena) : bits;
}

}  // namespace delta
