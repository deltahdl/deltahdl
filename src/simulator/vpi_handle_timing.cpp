#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

// ===========================================================================
// The vpi_handle() relations §37.40 draws from a timing check and from its
// tchk terms, and §37.39 from a module path and its path terms. Each reaches an
// object held as a designated pointer, its own type not being the relation's,
// so none is found by the generic walk over a handle's children. They sit in a
// file of their own because the resolvers they were written beside had grown to
// the length .github/workflows/deltahdl.yml admits a source file.
// ===========================================================================

// The field of a timing check holding what `type` reaches from it: detail 1's
// reference and data terms and the notifier register a violated check
// toggles. Null for a relation the check does not draw.
static VpiObject* VpiObject::* TchkField(int type) {
  if (type == vpiTchkRefTerm) return &VpiObject::tchk_ref_term;
  if (type == vpiTchkDataTerm) return &VpiObject::tchk_data_term;
  if (type == vpiTchkNotifier) return &VpiObject::tchk_notifier;
  return nullptr;
}

// The field of a tchk term holding what `type` reaches from it: the signal
// its event names, through the untagged arrow to `expr`, and the `&&&`
// condition the event was written with (§31.7), through vpiCondition. Null
// for a relation the term does not draw.
static VpiObject* VpiObject::* TchkTermField(int type) {
  if (type == vpiExpr) return &VpiObject::term_expr;
  if (type == vpiCondition) return &VpiObject::written_condition;
  return nullptr;
}

// The field of a module path or a path term holding what `type` reaches from
// `ref`: the condition a state-dependent path was written under (§30.4.4),
// and the terminal a path term stands for, through the untagged arrow to
// `expr`. Null for a relation the object does not draw.
static VpiObject* VpiObject::* PathField(int type, VpiHandle ref) {
  if (ref->type == vpiModPath && type == vpiCondition) {
    return &VpiObject::written_condition;
  }
  if (ref->type == vpiPathTerm && type == vpiExpr) return &VpiObject::term_expr;
  return nullptr;
}

bool TryResolveSpecifyRelation(int type, VpiHandle ref, VpiHandle& out) {
  VpiObject* VpiObject::* field = PathField(type, ref);
  if (ref->type == vpiTchk) field = TchkField(type);
  if (ref->type == vpiTchkTerm) field = TchkTermField(type);
  if (field == nullptr) return false;
  out = ref->*field;
  return true;
}

}  // namespace delta
