module HelloWorld

%default total

hello : Eff () [STDIO]
hello = putStrLn "Hello world!"

main : IO ()
main = run hello
