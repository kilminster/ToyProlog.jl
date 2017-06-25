using ToyProlog

myrules=Rulebase()

@rule myrules man(socrates)
@rule myrules man(pythagoras)
@rule myrules hates(socrates,drinks)
@rule myrules hates(pythagoras,beans)

println("What men do we know about?")
X=Variable()
g=@goal man(:X)
for env in prove(g,myrules)
    println(evaluate(X,env))
end
println()

println("What does pythagoras hate?")
g=@goal hates(pythagoras,:X)
for env in prove(g,myrules)
    println(evaluate(X,env))
end
println()

@rule myrules mortal(X) => man(X)
@rule myrules mortal(X) => woman(X)

@rule myrules woman(hypatia)

println("Is socrates mortal?")
g=@goal mortal(socrates)
for env in prove(g,myrules)
    println("Yes.")
end
println()

println("Who do we know who is mortal?")
g=@goal mortal(:X)
for env in prove(g,myrules)
    println(evaluate(X,env))
end
println()

@rule myrules legumeavoidingmortal(X) => mortal(X),hates(X,beans)

println("Who will die and avoids legumes?")
g=@goal legumeavoidingmortal(:X)
for env in prove(g,myrules)
    println(evaluate(X,env))
end
println()

# Fun with lists:

@rule myrules append(nil,X,X)
@rule myrules append(cons(H,T),B,cons(H,R)) => append(T,B,R)

println("Append [a,b,c] and [d,e]:")
g=@goal append(cons(a,cons(b,cons(c,nil))),
               cons(d,cons(e,nil)),
               :X)
for env in prove(g,myrules)
    println(evaluate(X,env))
end
println()

println("Find the last three elements of [a,b,c,d,e]")
Y=Variable()
Z=Variable()
g=@goal append(START,
               cons(:X,cons(:Y,cons(:Z,nil))),
               cons(a,cons(b,cons(c,cons(d,cons(e,nil))))))
for env in prove(g,myrules)
    println(evaluate(X,env)," ",evaluate(Y,env)," ",evaluate(Z,env))
end
println()

println("What lists concatenate to produce [a,b,c,d,e]?")
g=@goal append(:X,:Y,cons(a,cons(b,cons(c,cons(d,cons(e,nil))))))
for env in prove(g,myrules)
    println(evaluate(X,env),"    ",evaluate(Y,env))
end
println()
