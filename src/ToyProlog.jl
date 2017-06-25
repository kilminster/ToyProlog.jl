module ToyProlog

export Rulebase,Variable,@rule,@goal,prove,evaluate
import Base.show

abstract type Term end

immutable Atom <: Term
    name::String
end

show(io::IO,a::Atom)=write(io,a.name)

immutable Variable <: Term
    id::Int
end

variablecount=0
function Variable()
    global variablecount
    variablecount=variablecount+1
    Variable(variablecount)
end

show(io::IO,v::Variable)=write(io,"_$(v.id)")

immutable Compound <: Term
    functor::Atom
    args::Array{Term,1}
end

Compound(functor,args::Vararg{Term})=Compound(functor,Term[a for a in args])
(a::Atom)(args...)=Compound(a,args...)

function show(io::IO,c::Compound)
    show(io,c.functor)
    write(io,"(")
    if length(c.args)>0
        show(io,c.args[1])
        for a=c.args[2:end]
            write(io,",")
            show(io,a)
        end
    end
    write(io,")")
end


immutable Environment
    bindings::Dict{Variable,Term}
end
Environment()=Environment(Dict{Variable,Term}())


evaluate(a::Atom,env::Environment)=a

function evaluate(v::Variable,env::Environment)
    if haskey(env.bindings,v)
        evaluate(env.bindings[v],env)
    else
        v
    end
end

evaluate(c::Compound,env::Environment)=Compound(c.functor,Term[evaluate(a,env) for a in c.args])

addbinding(env,b)=Environment(merge(env.bindings,Dict(b)))


unify(t1,t2,env::Environment)=Channel() do c
    
    function u(t1::Term,t2::Term)
    end

    function u(a::Atom,b::Atom)
        if a.name==b.name
            put!(c,env)
        end
    end

    function u(v1::Variable,v2::Variable)
        if v1==v2
            put!(c,env)
            return
        end
        if !haskey(env.bindings,v1)
            put!(c,addbinding(env,v1=>v2))
            return
        end
        if !haskey(env.bindings,v2)
            put!(c,addbinding(env,v2=>v1))
            return
        end
        u(env.bindings[v1],env.bindings[v2])
    end

    function u(v::Variable,t::Term)
        if !haskey(env.bindings,v)
            put!(c,addbinding(env,v=>t))
        else
            u(env.bindings[v],t)
        end
    end

    u(t::Term,v::Variable)=u(v,t)

    function u(a1::Array{Term,1},a2::Array{Term,1})
        if length(a1)==length(a2)
            if length(a1)==0
                put!(c,env)
                return
            end
            for e1 in unify(a1[1],a2[1],env)
                for e2 in unify(a1[2:end],a2[2:end],e1)
                    put!(c,e2)
                end
            end
        end
    end

    function u(c1::Compound,c2::Compound)
        if c1.functor.name==c2.functor.name
            u(c1.args,c2.args)
        end
    end
    
    u(t1,t2)
end

type Rulebase
    rules::Dict{String,Array}
end
Rulebase()=Rulebase(Dict{Atom,Array}())

function addrule(rulebase,functor,rule)
    if !haskey(rulebase.rules,functor.name)
        rulebase.rules[functor.name]=[]
    end
    push!(rulebase.rules[functor.name],rule)
end

function getrules(rulebase,functor)
    if haskey(rulebase.rules,functor.name)
        return rulebase.rules[functor.name]
    else
        return []
    end
end

prove(goal,rulebase,env=Environment())=Channel() do c
    for rule in getrules(rulebase,goal.functor)
        for e in rule(goal,rulebase,env)
            put!(c,e)
        end
    end
end

function parseterm(ex::Symbol,context)
    name=string(ex)
    functor=nothing
    if name[1]==uppercase(name[1])
        context[ex]=:(Variable())
    else
        context[ex]=:(Atom($(name)))
        functor=ex
    end
    return ex,functor
end

function parseterm(ex::Expr,context)
    if ex.head==:call
        args=[parseterm(a,context)[1] for a in ex.args]
        functor=args[1]
        unshift!(args,:Compound)
        return Expr(:call,args...),functor
    end
    if ex.head==:quote
        return esc(ex.args[1]),nothing
    end
    println(ex)
    println(ex.head)
    println(ex.args)
    error("Don't understand term expression")
end

macro goal(ex)
    context=Dict()
    r=parseterm(ex,context)[1]
    for k in keys(context)
        r=quote
            let $(k)=$(context[k])
                $(r)
            end
        end
    end
    r
end

function parserule(ex::Expr,context)
    if ex.head==:call
        if ex.args[1]==:(=>)
            head,functor=parseterm(ex.args[2],context)
            subgoals=[]
            if ex.args[3].head==:call
                push!(subgoals,parseterm(ex.args[3],context)[1])
            end
            if ex.args[3].head==:tuple
                for ex1 in ex.args[3].args
                    push!(subgoals,parseterm(ex1,context)[1])
                end
            end
            r=quote
                put!(ch,env)
            end
            for g in reverse(subgoals)
                r=quote
                    for env in prove($(g),rulebase,env)
                        $(r)
                    end
                end
            end
            return quote
                for env in unify(goal,$(head),env)
                    $(r)
                end
            end,functor
        end
        fact,functor=parseterm(ex,context)
        return quote
            for env in unify(goal,$(fact),env)
                put!(ch,env)
            end
        end,functor
    end
end

macro rule(rulebase,ex)
    context=Dict()
    r,functor=parserule(ex,context)
    for k in keys(context)
        r=quote
            let $(k)=$(context[k])
                $(r)
            end
        end
    end
    functorstring=String(functor)
    r=quote
        ToyProlog.addrule($(esc(rulebase)),Atom($(functorstring)),function(goal,rulebase,env)
                Channel() do ch
                $(r)
                end
                end)
    end
    return r
end


end 
