"""Total generated integer-helper contracts, separate from C signed operators."""
from .terms import Type,U64,Node,Unsupported,number

MODEL='nirvana-c-integer-helpers-v2'
NAMES={'nirvana_sext8','nirvana_sext16','nirvana_sext32','nirvana_signed8','nirvana_signed16','nirvana_signed32',
       'nirvana_ashr64','nirvana_sdiv_word','nirvana_srem_word'}


def lower(g,name,args):
    if name.startswith('nirvana_sext') or name.startswith('nirvana_signed'):
        if len(args)!=1 or g.type(args[0])!=U64: raise Unsupported('integer helper signature')
        conversion=name.startswith('nirvana_signed')
        bits=int(name[len('nirvana_signed' if conversion else 'nirvana_sext'):]);value=g.cast(args[0],Type(bits))
        signed=g.intern(Node('bitcast',Type(bits,True),(value,)))
        return signed if conversion else g.cast(signed,U64)
    if name=='nirvana_ashr64':
        if len(args)!=2 or any(g.type(a)!=U64 for a in args): raise Unsupported('arithmetic shift helper signature')
        return g.intern(Node('total_ashr',U64,tuple(args)))
    if name not in ['nirvana_sdiv_word','nirvana_srem_word'] or len(args)!=3:
        raise Unsupported('integer helper name or arity')
    value,divisor,width=args;bits=g.constant(width);d=g.constant(divisor)
    if g.type(value)!=U64 or g.type(divisor)!=Type(64,True) or g.type(width)!=Type(32) or bits not in [8,16,32] or d is None:
        raise Unsupported('signed word helper requires a fixed width and divisor')
    d=number(d,g.type(divisor));word=Type(bits);value=g.cast(value,word);mask=(1<<bits)-1
    if -(1<<(bits-1))<=d<(1<<(bits-1)):
        quotient=g.intern(Node('total_sdiv',word,(value,g.const(d,word))))
    else:
        # The C helper's divisor is int64_t, not a truncated word divisor.
        sign=g.binary('>>',value,g.const(bits-1),word)
        magnitude=g.choose(sign,g.binary('-',g.const(0,word),value,word),value)
        q=g.const(0,word) if abs(d)>mask else g.binary('/',magnitude,g.const(abs(d),word),word)
        negative=g.binary('^',sign,g.const(int(d<0),word),word)
        quotient=g.choose(negative,g.binary('-',g.const(0,word),q,word),q)
    result=quotient if name=='nirvana_sdiv_word' else g.binary('-',value,g.binary('*',quotient,g.const(d,word),word),word)
    return g.cast(result,U64)
