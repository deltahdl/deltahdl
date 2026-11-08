#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

static VpiObject* VpiObject::* TchkField(int type) {
  if (type == vpiTchkRefTerm) return &VpiObject::tchk_ref_term;
  if (type == vpiTchkDataTerm) return &VpiObject::tchk_data_term;
  if (type == vpiTchkNotifier) return &VpiObject::tchk_notifier;
  return nullptr;
}

static VpiObject* VpiObject::* TchkTermField(int type) {
  if (type == vpiExpr) return &VpiObject::term_expr;
  if (type == vpiCondition) return &VpiObject::written_condition;
  return nullptr;
}

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
