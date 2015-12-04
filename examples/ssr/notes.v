 (s : (fun T : sort -> Type => prod (T Ty) (T Ter))
        (fun o0 : sort => var -> term o0)),
(s : prod ((fun o0 : sort => var -> term o0) Ty)
                ((fun o0 : sort => var -> term o0) Ter)),