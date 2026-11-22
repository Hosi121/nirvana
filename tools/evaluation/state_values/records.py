"""Immutable local record/view snapshots in the generated C model.

Declaration IDs and field-declaration order bind arbitrary records. The known
nirvana_view ABI has one uint64_t address, evaluated once at its setup site.
"""
from dataclasses import dataclass
from .. import state_memory as sm,c_footprint as cf
from .terms import U64,Unsupported


@dataclass(frozen=True)
class View:
    address:int


class Records:
    def __init__(self,graph,resolver): self.graph,self.resolver=graph,resolver

    def evaluate(self,node,state,value):
        node=sm.strip(node);kind=node.get('kind');parts=cf.children(node);g=self.graph
        def scalar(n):
            result=value(n,state)
            if g.type(result)!=U64: raise Unsupported('view address/index is not uint64_t')
            return result
        def view(n):
            result=self.evaluate(n,state,value)
            if not isinstance(result,View): raise Unsupported('unresolved captured view')
            return result
        if kind=='InitListExpr':
            if cf.type_key(node).replace('const ','')=='struct nirvana_view':
                if len(parts)!=1: raise Unsupported('view initializer shape')
                return View(scalar(parts[0]))
            if not cf.type_key(node).replace('const ','').startswith('struct '): raise Unsupported('record initializer type')
            return tuple(self.evaluate(n,state,value) for n in parts)
        if kind=='DeclRefExpr':
            identity=node.get('referencedDecl',{}).get('id')
            if identity in state.records: return state.records[identity]
        if kind=='MemberExpr' and not node.get('isArrow') and len(parts)==1:
            base=self.evaluate(parts[0],state,value)
            if isinstance(base,View):
                if node.get('name')!='address' or not sm.u64_type(node): raise Unsupported('view address field ABI')
                return base.address
            index=self.resolver.fields.get(node.get('referencedMemberDecl'))
            if not isinstance(base,tuple) or index is None or index>=len(base): raise Unsupported('unresolved record field')
            return base[index]
        if kind=='CallExpr':
            target,args=sm.callee(node),parts[1:]
            if target=='nirvana_location_address' and len(args)==1: return View(scalar(args[0]))
            if target=='nirvana_location_view' and len(args)==1: return view(args[0])
            if target=='nirvana_view_index' and len(args)==4:
                base=view(args[0]);index,stride,offset=[scalar(n) for n in args[1:]]
                delta=g.binary('+',g.binary('*',index,stride,U64),offset,U64)
                return View(g.binary('+',base.address,delta,U64))
        return value(node,state)
