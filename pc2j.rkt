#lang racket

(provide pc2j compile/run)

(define reg-funcs '())
(define union-funcs (set))
(define reg-pc 'no_pc)
(define dismount-var 'no_dis)
(define construct-var 'no_const)

(define global-decls '())
(define current-global-decls '())
(define main-def "")
(define union-defs "")
(define js-keywords
  ; Need to update
  '(False class from or None continue global pass True
          def if raise and del import return as elif
          in try assert else is while async except
          lambda with await finally nonlocal yield break
          for not))

(define add-func
  (lambda (func)
    (set! reg-funcs (cons func reg-funcs))))

(define is-func?
  (lambda (func)
    (assv func reg-funcs)))

(define add-union-func
  (lambda (func-name)
    (set! union-funcs (set-union union-funcs (set func-name)))))

(define is-global?
  (λ (var)
    (cond
      [(equal? (global var) reg-pc) #t]
      [(memv var reg-regs)
       => (λ (p) #t)]
      [else #f])))

(define reg-unions '())

(define check-args
  (lambda (union args)
    (cond
      [(null? args) #t]
      [(memq (car args) (cdr args))
       (error 'define-union "duplicated variant `~a' in union `~a'\n" (car args) (car union))]
      [else (check-args union (cdr args))])))

(define add-union
  (lambda (union)
    (if (not (lookup-union (car union)))
        (begin (check-args union (cadr union))
               (set! reg-unions (cons union reg-unions)))
        (error 'define-union "duplicated definition of union-type `~a'\n" (car union)))))

(define reg-regs '())

(define init-storage
  (lambda ()
    (set! reg-funcs '())
    (set! reg-unions '())
    (set! reg-regs '())))

(define new-safe-char
  (lambda (char)
    (cond
      [(eq? #\? char) "_"]
      [(eq? #\! char) "_"]
      [(eq? #\. char) "_"]
      [(eq? #\+ char) "_"]
      [(eq? #\- char) "_"]
      [(eq? #\* char) ""]
      [(eq? #\/ char) "_"]
      [(eq? #\< char) "_"]
      [(eq? #\> char) "_"]
      [(eq? #\: char) "_"]
      [(eq? #\% char) "_"]
      [(eq? #\^ char) "_cap"]
      [(eq? #\& char) "_"]
      [(eq? #\~ char) "_"]
      [(eq? #\_ char) "_"]
      [(and (char>=? char #\0) (char<=? char #\9))
       (string-append "r" (list->string `(,char)))]
      [else (list->string `(,char))])))

(define safe
  (lambda (sym)
    (let ([str-sym (raw-safe sym)])
      (cond
        [(memv sym js-keywords)
         => (λ (p) (string-append "_" str-sym))]
        [else str-sym]))))

(define raw-safe
  (lambda (sym)
    (if (symbol? sym)
        (let loop ([l (string->list (symbol->string sym))])
          (cond
            [(null? l) ""]
            [else (string-append
                   (new-safe-char (car l))
                   (loop (cdr l)))]))
        sym)))

(define make-titlecase
  (lambda (name)
    (join (map string-titlecase (string-split name "-")) "")))

(define global
  (lambda (sym)
    (string-append "Register_" (string-upcase (safe sym)))))

(define join
  (lambda (lst separater)
    (let loop ([lst lst]
               [result ""]
               [is-first? #t])
      (cond
        [(null? lst) result]
        [is-first? (loop (cdr lst)
                         (format "~a" (car lst)) #f)]
        [else (loop (cdr lst)
                    (string-append
                     result
                     (format "~a~a" separater (car lst)))
                    #f)]))))

(define file->list
  (lambda (fname)
    (let ([file (open-input-file fname)])
      (let ([data
             (let recurse ([decl (read file)])
               (if (eof-object? decl)
                   '()
                   (cons decl (recurse (read file)))))])
        (close-input-port file)
        data))))

(define application-name "program")
(define pc2j
  (lambda (file-name source-name)
    ;; WARNING: pc2j will erase existing files when generating new ones!
    (set! application-name
          (join (drop-right (string-split source-name ".") 1) "."))
    (when (file-exists? source-name) (delete-file source-name))
    (init-storage)
    (let ([decl* (file->list file-name)])
      (let ([src (open-output-file source-name)])
        (dynamic-wind
         (lambda () #f)
         (lambda ()
           ;; write a generated header file to header-name
           (display (pc2j-header decl*) src)
           (check-correct-info)
           ;; write a generated source file source-name
           (display (pc2j-source) src)
           (set! global-decls '())
           (set! union-defs ""))
         (lambda ()
           (close-output-port src)))))))

(define check-correct-info
  (lambda ()
    (begin
      (if (null? reg-regs)
          (display "Warning: you have defined no registers.\n")
          (void)))))

(define pc2j-append
  (lambda args
    (apply string-append
           (map (lambda (elt)
                  (cond
                    [(symbol? elt) (format "~a" elt)]
                    [(number? elt) (format "~s" elt)]
                    [(string? elt) elt]
                    [else (error 'pc2j-append "Invalid argument ~s" elt)]))
                args))))

(define pc2j-gen-unions
  (lambda (union)
    (let ([name (safe (car union))]
          [tag* (cadr union)]
          [field** (caddr union)])
      (apply string-append
             (map (lambda (tag field*)
                    (let* ([safe-tag (safe tag)]
                           [fnname (cond
                                     [(memv tag js-keywords)
                                      => (λ (p) (pc2j-append name safe-tag))]
                                     [else (pc2j-append name "_" safe-tag)])])
                      (pc2j-append
                       (pc2j-fn-proto fnname field*)
                       " {\n"
                       "        HashMap<String, Object> properties = new HashMap<>();\n"
                       (string-join (map (λ (v)
                                           (string-append
                                            "        properties.put(\"" (safe v) "\", " (safe v) ");"))
                                         field*)
                                    "\n")
                       "\n        return new UnionType(UnionEnums." name "." (string-upcase safe-tag) ", properties);\n"
                       "    }\n\n")))
                  tag* field**)))))

;; added by wy for constructor argument name binding
;; lookup-arg looks up the argument name of name.tag at position pos
(define lookup-union
  (lambda (name)
    (let loop ([reg reg-unions])
      (cond
        [(null? reg) #f]
        [(eq? name (caar reg)) (car reg)]
        [else (loop (cdr reg))]))))

(define get-arg-list
  (lambda (name tag)
    (let ([u (lookup-union name)])
      (if (not u) (error 'lookup-union
                         "union type `~a' not defined\n" name)
          (let loop ([tags (cadr u)] [args (caddr u)])
            (cond
              [(null? tags)
               (error 'lookup-arg
                      "union type `~a' doesn't have a tag `~a'~n" name tag)]
              [(eq? tag (car tags)) (car args)]
              [else (loop (cdr tags) (cdr args))]))))))

(define lookup-arg
  (lambda (name tag pos)
    (list-ref (get-arg-list name tag) pos)))

(define check-union-case
  (lambda (expr name type case)
    (cond
      [(and (null? type) (not (null? case)))
       (let ([s (open-output-string)])
         (pretty-print expr s)
         (error 'union-case  "~a\nsuperfluous cases for union type `~a': ~a"
                (get-output-string s) name case))]
      [(and (null? case) (not (null? type)))
       (let ([s (open-output-string)])
         (pretty-print expr s)
         (error 'union-case  "~a\nunmatched cases for union type `~a': ~a"
                (get-output-string s) name type))]
      [(and (null? type) (null? case)) #t]
      [(not (memq (car case) type))
       (let ([s (open-output-string)])
         (pretty-print expr s)
         (error 'union-case "~a\nvariant `~a' is not in union type `~a'"
                (get-output-string s) (car case) name))]
      [(memq (car case) (cdr case))
       (let ([s (open-output-string)])
         (pretty-print expr s)
         (error 'union-case  "~a\nduplicated cases `~a' in union-case of type `~a'"
                (get-output-string s) (car case) name))]
      [else (check-union-case expr name (remq (car case) type) (cdr case))])))

(define case-env
  (lambda (env var*)
    (let loop ([env env] [var* var*])
      (if (null? var*)
          env
          (extend-env (car var*) (car var*) (loop env (cdr var*)))))))

(define handle-union-case-case
  (lambda (name env u_obj)
    (lambda (template body)
      (match template
        [`(,tag . ,var*)
         #:when (list? var*)
         (set! error-thrown #f)
         (let ([sname (safe name)]
               [stag (safe tag)])
           (let ([given (length var*)] [expected (length (get-arg-list name tag))])
             (let ([ret-val
                    (if (not (= given expected))
                        (error 'union-case
                               "~a\nwrong number of arguments to constructor `~a' of union-type `~a': expected: ~a, given: ~a"
                               template tag name expected given)
                        (pc2j-append
                         "            case " (string-upcase stag) ":\n"
                         (let loop ([var* var*] [n 0])
                           (cond
                             [(null? var*) ""]
                             [else
                              (string-append
                               (pc2j-append
                                "                " (safe (car var*)) " = union_object.get(\"" (safe (lookup-arg name tag n)) "\");\n")
                               (loop (cdr var*) (add1 n)))]))
                         ((parse-function-body #t (case-env env var*) 4) body)
                         (cond
                           [error-thrown "\n\n"]
                           [else "                break;\n\n"])))])
               (set! error-thrown #f)
               ret-val)))]
        ;; Cannot possibly be effective, commented JBH 12/13
        ;; [else (string-append "default {\n"
        ;;         ((parse-function-body #t (case-env env var*)) body)
        ;;         "}\n")]
        ))))

(define get-last
  (lambda (ls)
    (cond
      ((null? ls) #f)
      ((null? (cdr ls)) (car ls))
      (else (get-last (cdr ls))))))

;; this is for error checking
(define get-body
  (lambda (c)
    (match c
      [`(,test ,body) body])))

(define remove-last
  (lambda (ls)
    (match ls
      [`((else ,body)) '()]
      [`((,test ,body) . ,c*) `((,test ,body) . ,(remove-last c*))])))

(define apply-env
  (lambda (env x)
    (match env
      [`(empty-env) (error 'empty-env "unbound variable: ~s" x)]
      [`(extend-env ,x^ ,a ,env)
       (if (eq? x^ x) a (apply-env env x))])))

(define extend-env
  (lambda (x a env)
    `(extend-env ,x ,a ,env)))

(define empty-env
  (lambda ()
    `(empty-env)))

(define tabs
  (lambda (n)
    (cond
      [(zero? n) ""]
      [else (string-append "    " (tabs (sub1 n)))])))

(define error-thrown #f)
(define parse-function-body
  (lambda (tail env level [main #f])
    (if tail
        (lambda (expr)
          (match expr
            [`(error ,name ,msg)
             (set! error-thrown #t)
             (pc2j-append
              (tabs level) "throw new Exception(\"" msg "\");\n")]
            [`(if ,test ,conseq ,alt)
             (let ((test ((parse-function-body #f env (add1 level) main) test))
                   (conseq ((parse-function-body #t env (add1 level) main) conseq))
                   (alt ((parse-function-body #t env (add1 level) main) alt)))
               (pc2j-append
                (tabs level) "if ((Boolean) (" test ")) {\n"
                conseq
                (tabs level) "} else {\n"
                alt
                (tabs level) "}\n"))]
            [`(cond (else ,body))
             (let ((body ((parse-function-body #t env level main) body)))
               body)]
            [`(cond . ,c*)
             (let ((last (get-last c*))
                   (c* (remove-last c*)))
               (cond
                 [(eq? (car last) 'else)
                  (let* ((test0 ((parse-function-body #f env level main) (caar c*)))
                         (body0 ((parse-function-body #t env (add1 level) main) (get-body (car c*))))
                         (test* (map (parse-function-body #f env level main) (map car (cdr c*))))
                         (body* (map (parse-function-body #t env (add1 level) main) (map get-body (cdr c*))))
                         (body ((parse-function-body #t env (add1 level) main) (cadr last))))
                    (pc2j-append
                     (tabs level) "if ((Boolean) (" test0 ")) {\n" body0 "\n"
                     (apply string-append
                            (map (lambda (x y)
                                   (pc2j-append (tabs level) "} else if (" x ") {\n"
                                                y))
                                 test* body*))
                     (tabs level) "} else {\n" body "    }\n"))]
                 [else
                  (let* ((test0 ((parse-function-body #f env level main) (caar c*)))
                         (body0 ((parse-function-body #t env level main) (cadar c*)))
                         (test* (map (parse-function-body #f env level main) (map car (cdr c*))))
                         (body* (map (parse-function-body #t env level main) (map cadr (cdr c*)))))
                    (pc2j-append
                     "if ((Boolean) (" test0 ")) {\n"
                     "    " body0 "\n"
                     (apply string-append
                            (map (lambda (x y)
                                   (pc2j-append "} else if (" x ") {\n"
                                                y))
                                 test* body*))
                     "}\n"))]))]
            [`(begin . ,expr*)
             (apply string-append (map (parse-function-body #t env level main) expr*))]
            [`(set! ,var ,var1) #:when (eq? var var1) ""]
            [`(set! ,var ,val)
             (let ((val ((parse-function-body #f env level main) val)))
               (if (is-global? var)
                   (begin
                     (set! current-global-decls (remove-duplicates (cons (global var) current-global-decls)))
                     (pc2j-append (tabs level) "RegistersGlobal." (global var) " = "
                                  (cond
                                    [(equal? (global var) reg-pc)
                                     (string-append
                                      "() -> {\n"
                                      (tabs (add1 level)) (string-trim val) "();\n"
                                      (tabs (add1 level)) "return null;\n"
                                      (tabs level) "}")]
                                    [else
                                     (string-trim val)])
                                  ";\n"))
                   (pc2j-append (tabs level) (safe var) " = " (string-trim val) "\n")))]
            [`(union-case ,val ,name . ,c*)
             (let ((template* (map car c*))
                   (body* (map get-body c*)))
               (define var-declarations
                 (set->list
                  (foldr
                   (lambda (a b) (set-union a b))
                   (set)
                   (map (lambda (t)
                          (match t
                            [`(,tag . ,var*) (list->set var*)]))
                        template*))))
               (if (not (check-union-case expr name
                                          (cadr (or (lookup-union name)
                                                    (error 'lookup-union
                                                           "union type `~a' not defined ~n" name)))
                                          (map car template*)))
                   (error 'union-case "union-case doesn't match definition: `~a'\n"
                          name)
                   (letrec ([sname (safe name)]
                            [target_u_obj (global val)]
                            [cases (apply string-append
                                          (map (handle-union-case-case name env target_u_obj)
                                               template*
                                               body*))])
                     (pc2j-append
                      "        UnionType union_object = ((UnionType) RegistersGlobal." target_u_obj ");\n"
                      "        UnionEnums." name " target = (UnionEnums." name ") union_object.getType();\n\n"
                      (string-append
                       "        Object "
                       (join
                        (map (lambda (v)
                               (string-append
                                (safe v) " = null"))
                             var-declarations)
                        ", ")
                       ";\n\n")
                      "        switch (target) {\n"
                      cases
                      "        }\n"))))]
            [`(let ,bind* ,body)
             (let ((lhs* (map car bind*))
                   (rhs* (map (parse-function-body #f env level main) (map cadr bind*))))
               (pc2j-append
                "\n"
                (apply string-append
                       (map (lambda (x y)
                              (pc2j-append
                               "var " (safe x) " = " y ";\n"))
                            lhs* rhs*))
                body
                "\n"))]
            [`(printf ,str . ,parms*)
             (string-append (tabs level)
                            "System.out.printf("
                            (join (cons (string-replace
                                         (string-replace
                                          (string-replace
                                           (format "~s" str)
                                           "~v" "%d")
                                          "~a" "%d")
                                         "~s" "%d")
                                        (map (λ (s)
                                               (cond
                                                 [(is-global? s) (string-append
                                                                  "RegistersGlobal."
                                                                  (global s))]
                                                 [else (safe s)]))
                                             parms*))
                                  ", ") ");\n")]
            [`(mount-trampoline ,construct ,dismount ,pc)
             (set! construct-var (safe construct))
             (set! dismount-var (global dismount))
             (pc2j-append
              (tabs level) "application.continuationDriver.mount_tram();\n"
              (tabs level) "application.continuationDriver.waitUntilTrampolineTermination();\n")]
            [`(dismount-trampoline ,dismount)
             (pc2j-append (tabs level) "this.executorService.submit((Callable<Void>) jumpout);")]
            [`(,func) #:when (is-func? func)
                      (pc2j-append "RegistersGlobal." reg-pc " = () -> { " (safe func) "; return null; };\n")]
            [`,elsee
             (let ((elsee ((parse-function-body #f env level main) elsee)))
               (pc2j-append "return " elsee ";\n"))]
            ))
        (lambda (expr)
          (match expr
            ;; [(error ,name ,msg)
            ;;  (pc2j-append
            ;;   "fprintf(stderr, \"" msg "\");\n exit(1);\n")]
            [`#t  (pc2j-append "true")]
            [`#f  (pc2j-append "false")]
            [`,x
             #:when (symbol? x)
             (letrec ([var (apply-env env x)]
                      [safe-x (safe var)])
               (cond
                 [(is-global? var)
                  (begin
                    (set! current-global-decls
                          (remove-duplicates
                           (cons (global var)
                                 current-global-decls)))
                    (string-append "RegistersGlobal." (global var)))]
                 [(and main (dict-has-key? reg-funcs x))
                  (string-append "application.continuationDriver." safe-x)]
                 [(dict-has-key? reg-funcs x)
                  (string-append "this." safe-x)]
                 [(set-member? union-funcs safe-x)
                  (string-append "UnionType." (global var))]
                 [else safe-x]))]
            [`,x #:when (integer? x) (pc2j-append x)]
            [`(zero? ,x)
             (let ((x ((parse-function-body #f env level main) x)))
               (pc2j-append "" x ".equals(0)"))]
            [`(and ,a ,b)
             (let ((a ((parse-function-body #f env level main) a))
                   (b ((parse-function-body #f env level main) b)))
               (pc2j-append "((Boolean)" a " && (Boolean) " b ")"))]
            [`(or ,a ,b)
             (let ((a ((parse-function-body #f env level main) a))
                   (b ((parse-function-body #f env level main) b)))
               (pc2j-append "((Boolean) " a " || (Boolean) " b ")"))]
            [`(not ,x)
             (let ((x ((parse-function-body #f env level) x)))
               (pc2j-append "(!(Boolean) " x ")"))]
            [`(< ,a ,b)
             (let ((a ((parse-function-body #f env level main) a))
                   (b ((parse-function-body #f env level main) b)))
               (pc2j-append "((Integer) " a " < (Integer) " b ")"))]
            [`(> ,a ,b)
             (let ((a ((parse-function-body #f env level main) a))
                   (b ((parse-function-body #f env level main) b)))
               (pc2j-append "((Integer) " a " > (Integer) " b ")"))]
            [`(<= ,a ,b)
             (let ((a ((parse-function-body #f env level main) a))
                   (b ((parse-function-body #f env level main) b)))
               (pc2j-append "((Integer) " a " <= (Integer) " b ")"))]
            [`(>= ,a ,b)
             (let ((a ((parse-function-body #f env level main) a))
                   (b ((parse-function-body #f env level main) b)))
               (pc2j-append "((Integer) " a " >= (Integer) " b ")"))]
            [`(+ ,a ,b)
             (let ((a ((parse-function-body #f env level main) a))
                   (b ((parse-function-body #f env level main) b)))
               (pc2j-append "(Integer) " a " + (Integer) " b))]
            [`(* ,a ,b)
             (let ((a ((parse-function-body #f env level main) a))
                   (b ((parse-function-body #f env level main) b)))
               (pc2j-append "(Integer) " a " * (Integer) " b))]
            [`(- ,a ,b)
             (let ((a ((parse-function-body #f env level main) a))
                   (b ((parse-function-body #f env level main) b)))
               (pc2j-append "(Integer) " a " - (Integer) " b))]
            [`(/ ,a ,b)
             (let ((a ((parse-function-body #f env level main) a))
                   (b ((parse-function-body #f env level main) b)))
               (pc2j-append "(Integer) " a " / (Integer) " b))]
            [`(sub1 ,a)
             (let ((a ((parse-function-body #f env level main) a)))
               (pc2j-append "((Integer) " a " - 1)"))]
            [`(add1 ,a)
             (let ((a ((parse-function-body #f env level main) a)))
               (pc2j-append "((Integer) " a " + 1)"))]
            [`(random ,x)
             (let ((x ((parse-function-body #f env level main) x)))
               (pc2j-append "(int) (Math.random() * " x ")"))]
            [`(if ,test ,conseq ,alt)
             (let ((test ((parse-function-body #f env 0 main) test))
                   (conseq ((parse-function-body #f env 0 main) conseq))
                   (alt ((parse-function-body #f env 0 main) alt)))
               (pc2j-append "(" conseq ") ? (" test ") : (" alt ")"))]
            [`(,func . ,args*) #:when (symbol? func)
                               (let ((args* (map (parse-function-body #f env level main) args*))
                                     (safe-func (cond
                                                  [(set-member? union-funcs (safe func))
                                                   (string-append "UnionType." (safe func))]
                                                  [else (safe func)])))
                                 (pc2j-append (tabs level)
                                              safe-func "(" (join args* ", ") ")"))])))))

(define pc2j-gen-funcs
  (lambda (env)
    (lambda (func)
      (let ([name (safe (car func))]
            [body (cadr func)])
        (if (equal? name "main")
            (begin
              (set! main-def (pc2j-append
                              (pc2j-append
                               "public class " application-name " {\n"
                               "\n"
                               "    private ContinuationDriver continuationDriver;\n"
                               "\n"
                               "    public " application-name "() {\n"
                               "        this.continuationDriver = new ContinuationDriver(Executors.newSingleThreadExecutor());\n"
                               "    }\n"
                               "\n"
                               "    public static void main(String[] args) throws InterruptedException {\n"
                               "        " application-name " application = new " application-name "();\n")
                              ((parse-function-body #t env 2 #t) body)
                              "    }\n"
                              "}\n"))
              "")

            (begin
              (pc2j-append
               (pc2j-append "    public Future<Void> " name "() throws Exception {\n")
               ((parse-function-body #t env 1) body)
               "        return null;\n"
               "    }\n\n")))))))

(define global-env
  (lambda ()
    (let loop ([env (empty-env)]
               [reg (append (map car reg-funcs) reg-regs)])
      (if (null? reg)
          env
          (extend-env (car reg) (car reg) (loop env (cdr reg)))))))

(define pc2j-source
  (lambda ()
    (let* ([s2 (apply string-append (map (pc2j-gen-funcs (global-env)) reg-funcs))])
      (let ([s3 (join
                 (list
                  "    void mount_tram() {"
                  (string-append
                   "        RegistersGlobal." dismount-var " = UnionType." construct-var "((Callable<Void>) (() -> {")
                  "            this.executorService.shutdown();"
                  "            return null;"
                  "        }));"
                  ""
                  "        trampoline();"
                  "    }"
                  ""
                  "    void trampoline() {"
                  (string-append
                   "        this.executorService.submit(RegistersGlobal." reg-pc ");")
                  "        this.executorService.submit(() -> {"
                  "            trampoline();"
                  "            return null;"
                  "        });"
                  "    }"
                  ""
                  "    void waitUntilTrampolineTermination() throws InterruptedException {"
                  "        this.executorService.awaitTermination(Long.MAX_VALUE, TimeUnit.NANOSECONDS);"
                  "    }"
                  "}\n\n")
                 "\n")])
        (string-append
         "// Generate functions\n"
         (join
          (list
           "class ContinuationDriver {"
           ""
           "    private ExecutorService executorService;"
           ""
           "    public ContinuationDriver(ExecutorService executorService) {"
           "        this.executorService = executorService;"
           "    }"
           "\n")
          "\n")
         s2
         s3
         "\n"
         main-def)))))

(define pc2j-header
  (lambda (decl*)
    (string-append
     "import java.util.HashMap;\n"
     "import java.util.concurrent.Callable;\n"
     "import java.util.concurrent.ExecutorService;\n"
     "import java.util.concurrent.Executors;\n"
     "import java.util.concurrent.Future;\n"
     "import java.util.concurrent.TimeUnit;\n\n"
     (apply string-append
            (map pc2j-header-parse decl*))
     (string-append
      "// Define the registers\n"
      (if (null? reg-regs)
          ""
          (string-append
           "class RegistersGlobal {\n"
           (join (map (λ (v)
                        (let ([global-new (global v)])
                          (set! global-decls (cons global-new global-decls))
                          (string-append "    static Object " global-new " = null;"))) reg-regs) "\n")
           (string-append
            "\n\n    // Define the program counter\n"
            "    static Callable<Void> " reg-pc " = null;\n")
           "}\n\n")))
     "// Define the union classes, functions and enums\n"
     "class UnionEnums {\n"
     union-defs
     "}\n\n"
     "// Define the union classes\n"
     (join
      (list
       "class UnionType extends Object {"
       ""
       "    private Object type = null;"
       "    private HashMap<String, Object> properties = new HashMap<>();"
       ""
       "    public Object getType() {"
       "        return type;"
       "    }"
       ""
       "    public Object get(String property) {"
       "        return this.properties.get(property);"
       "    }"
       ""
       "    public UnionType(Object type, HashMap<String, Object> properties) {"
       "        this.type = type;"
       "        this.properties = properties;"
       "    }"
       ""
       "    @Override"
       "    public String toString() {"
       "        return \"UnionType[type = \" + type.toString() + \", properties = {\""
       "                + properties.keySet().stream().map((String s) -> {"
       "                    return s + \": \" + properties.get(s).toString();"
       "                }).reduce(\"\", (String a, String p) -> {"
       "                    return a + \", \" + p;"
       "                }) + \"}]\";"
       "    }\n"
       "    // Union functions"
       (apply string-append (map pc2j-gen-unions reg-unions))
       "}\n\n")
      "\n"))))

(define pc2j-header-parse
  (lambda (decl)
    (match decl
      [`(load ,file . ,file*)  ""]
      [`(exit)  ""]
      [`(display ,anything . ,anything*)  ""]
      [`(pretty-print ,anything . ,anything*)  ""]
      [`(define-registers . ,reg*)
       (set! reg-regs reg*)
       ""]
      [`(define-program-counter ,pc)
       (set! reg-pc (global pc))
       ""]
      [`(define-union ,name . ,c*)
       (let ((tag* (map car c*))
             (field** (map cdr c*)))
         (add-union `(,name ,tag* ,field**))
         (let ([name (safe name)])
           (let ([enum-values
                  (apply string-append
                         (map
                          (lambda (tag field* index)
                            (let ([tag (safe tag)])
                              (format "       ~a,\n" (string-upcase tag))))
                          tag* field** (range (length tag*))))])
             (set! union-defs
                   (string-append union-defs
                                  (pc2j-append
                                   ;"class " name "_t(object):\n"
                                   "    enum " name " {\n"
                                   enum-values
                                   "    }\n\n")))
             "")))]
      [`(define-label ,name ,body) ""
                                   (begin (add-func `(,name ,body))
                                          "" #;(string-append (if (equal? (safe name) "main")
                                                                  "int "
                                                                  "void ") (safe name) "();\n"))])))

(define pc2j-fn-proto
  (lambda (fn-name param*)
    (let ([declare-params
           (lambda (param*)
             (join (map (lambda (param)
                          (format "Object ~a" (safe param))) param*) ", "))])
      (add-union-func fn-name)
      (pc2j-append
       "    public static UnionType " (safe fn-name) "(" (declare-params param*)  ")"))))

(define compile/run
  (lambda (base-name)
    (let ([pc-file (string-append base-name ".pj")]
          [java-file (string-append base-name ".java")])
      (pc2j pc-file java-file)
      (system (string-append "javac ./" java-file "; java " base-name ".class")))))
