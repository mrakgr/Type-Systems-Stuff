Currently, I am in process of translating the [examples](https://www.cis.upenn.edu/~bcpierce/tapl/) from Pierce's Types and Programming Languages from Ocaml to F#.

Edit: Change of plans, rather than translate all the examples, I'll make this an experimental repo for the examples I am interested in.

2/25/2017: Well, this repo went nowhere. To be honest, while I did succeed in figuring out algorithm W and bidirectional typechecking, those papers linked to me on the types subreddit are beyond me, in particular the ['easy' paper](https://people.mpi-sws.org/~neelk/bidir.pdf) which relies on algorithmic context is kind of an automated proof tactic; no way I'll be able to figure that one out. All these methods that rely on global communication are too complicated for me.

That I'd be better off hacking out something on my own is what I have concluded.

And these three and a half weeks that I've been studying this for have given me a lot of ideas. At the very least, I now understand how to do local type inference and with some tricks and tradeoffs, I will be able to make it global. The things I intend to do would absolutely wreck editor support (much like macros) but I will get the expressive power of higher ranked and dependently typed functions that I seek.

In the end, doing this made me appreciate how difficult inference is and I will no longer make unreasonable demands of F# or any other language.

I am glad I made those posts on the types sub, before that I've never even heard of bidirectional type checking.

Today I will charge my energy and tomorrow I will make my fourth attempt at making that Cuda backend.

-----

Some good references on bidirectional typechecking:

https://people.mpi-sws.org/~joshua/bitype.pdf
http://davidchristiansen.dk/tutorials/bidirectional.pdf
https://jozefg.bitbucket.io/posts/2014-11-22-bidir.html
