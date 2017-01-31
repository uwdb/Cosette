#lang rosette

(require "../table.rkt" "../evaluator.rkt" "../sql.rkt")

;(struct input ([user_id, path, email]))
(define project-tbl (Table "project" (list "id" "path" "group_id" "public" "archived") (gen-sym-schema 5 1)))
(define project-group-link-tbl (Table "projectgrouplink" (list "id" "project_id" "access_level") (gen-sym-schema 3 1)))
(define namespace-tbl (Table "namespace" (list "id" "owner_id" "project_id") (gen-sym-schema 3 1)))
(define member-tbl (Table "member" (list "id" "user_id" "project_id" "access_level" "group_id") (gen-sym-schema 5 1)))
(define user-tbl (Table "user" (list "id" "is_admin" "external" "email") (gen-sym-schema 4 1)))
(define group-tbl (Table "group" (list "id" "project_link_id") (gen-sym-schema 2 1)))
(define email-tbl (Table "email" (list "id" "email" "user_id") (gen-sym-schema 3 1)))
(define event-tbl (Table "event" (list "id" "author_id" "project_id" "action" "target_id" "target_type") (gen-sym-schema 6 1)))

(define (query-user1 param)
  (SELECT (VALS "user.id" "user.external" "user.is_admin" "user.email")
          FROM (NAMED user-tbl)
          WHERE (BINOP "user.id" = param)))

(define (query-project2 param)
  (SELECT (VALS "project.id" "project.path" "project.group_id" "project.public" "project.archived")
          FROM (NAMED project-tbl)
          WHERE (BINOP "project.path" = param)))

(define (query-project-members3 param)
  (SELECT (VALS "member.user_id" "member.access_level" "member.id")
          FROM (NAMED member-tbl)
          WHERE (BINOP "member.project_id" = param)))

(define (query-project-group4 param)
  (SELECT (VALS "group.id")
          FROM (NAMED group-tbl)
          WHERE (BINOP "group.id" = param)))

(define (helper-get-member-user-id param)
  (SELECT (VALS "user.id")
          FROM (JOIN (NAMED user-tbl) (NAMED member-tbl))
          WHERE (AND (BINOP "member.user_id" = "user.id") (BINOP "member.id" = param))))

(define (query-project-group-members5 param)
  (SELECT (VALS "member.user_id" "member.access_level" "member.id")
          FROM (JOIN (NAMED member-tbl) (NAMED group-tbl))
          WHERE (AND (BINOP "member.group_id" = "group.id") (BINOP "group.id" = param))))

(define (query-project-group-link6 param)
  (SELECT (VALS "projectgrouplink.project_id" "projectgrouplink.access_level")
          FROM (NAMED project-group-link-tbl)
          WHERE (BINOP "projectgrouplink.project_id" = param)))

(define (query-group-link-groups7 param)
  (SELECT (VALS "group.id")
          FROM (JOIN (NAMED group-tbl) (NAMED project-group-link-tbl))
          WHERE (AND (BINOP "group.project_link_id" = "projectgrouplink.id") (BINOP "projectgrouplink.project_id" = param))))

(define (query-group-link-groups-members8 param1 param2)
  (SELECT (VALS "member.access_level")
          FROM (NAMED member-tbl)
          WHERE (AND (BINOP "member.group_id" = param1) (BINOP "member.user_id" = param2))))

(define (query-project-namespace9 param)
  (SELECT (VALS "namespace.owner_id")
          FROM (NAMED namespace-tbl)
          WHERE (BINOP "namespace.project_id" = param)))

(define (query-project-namespace-owner10 param)
  (SELECT (VALS "user.id" "user.external" "user.is_admin" "user.email")
          FROM (JOIN (NAMED user-tbl) (NAMED namespace-tbl))
          WHERE (AND (BINOP "user.id" = "namespace.owner_id") (BINOP "namespace.project_id" = param))))

(define (query-project-group-members-user11 param1 param2)
  (SELECT (VALS "user.id")
          FROM (NAMED user-tbl)
          WHERE (AND (BINOP "user.id" = param1) (BINOP "user.id" = param2))))

(define (query-project-project-members-aclevel12 param1 param2)
  (SELECT (VALS "member.id")
          FROM (NAMED member-tbl)
          WHERE (AND (BINOP "member.id" = param1) (BINOP "member.access_level" = param2))))
  
(define (query-project-events13 param)
  (SELECT (VALS "event.action" "event.target_id" "event.target_type")
          FROM (NAMED event-tbl)
          WHERE (EXISTS
                 (SELECT (VALS "user.id")
                         FROM (NAMED user-tbl)
                         WHERE (AND (BINOP "event.project_id" = param) (BINOP "user.id" = "event.author_id"))))))

(define (query-event-author14 param)
  (SELECT (VALS "user.id")
          FROM (NAMED user-tbl)
          WHERE (BINOP "user.id" = param)))

(define (query-user-by-email15 param)
  (SELECT (VALS "user.id")
          FROM (JOIN (NAMED user-tbl) (NAMED email-tbl))
          WHERE (AND (BINOP "user.id" = "email.user_id") (BINOP "email.email" = param))))

(define (get-symbolic-int)
  (define-symbolic* in integer?)
  (assert (>= in 0))
  in)

(define (get-symbolic-int-array n)
  (build-list n (lambda(x) (get-symbolic-int))))

(define (list-recur-with-param f l p)
  (cond
    [(empty? l) #f]
    [else (or (f (first l) p) (list-recur-with-param f (rest l) p))]
  ))

(define (execute-program ins)
  (let* (;current_user = User.where(:id => params[:user_id]).first // query-user1
         [q1 (get-content (run (query-user1 (first ins))))]
         [current_user (car (first q1))]
         ;project = Project.where(:path => params[:path]).first // query-project2
         [q2 (get-content (run (query-project2 (second ins))))]
         [project (car (first q2))]
         ;project.project_members // query-project-members3, param: project.id
         [q3 (get-content (run (query-project-members3 (first project))))]
         [project-project_members q3]
         ;project.project_members.each do |member|
         [loop-br1-func (lambda (m userid) (
                               let* (;loop-v1 = member.user_id)
                                     [loop-v1 (first (car m))]
                                     ;if member.user_id == current_user.id
                                     ;[loop-v2 (= loop-v1 userid)])
                                     ;Alternative: loop-v1 = member.user.id
                                     [loop-q (get-content (run (helper-get-member-user-id (third (car m)))))]
                                     [loop-v1 (first (car (first loop-q)))]
                                     [loop-v2 (= loop-v1 userid)])
                                     loop-v2))]
         [loop-br1 (list-recur-with-param loop-br1-func project-project_members (first current_user))]
         ;XXX: Make sure it enters the loop
         [br1 (and (not (empty? project-project_members)) loop-br1)]
         [untaken-br1 (and (not (empty? project-project_members)) (not loop-br1))]
         ;if project.group // query-project-group4
         [q4 (get-content (run (query-project-group4 (third project))))]
         [br2 (not (empty? q4))]
         [untaken-br2 (empty? q4)]
         ;project.group.members.each do |member| // query-project-group-members5
         [q5 (get-content (run (query-project-group-members5 (third project))))]
         [loop-br3-func (lambda (m userid) (
                                            let* (;loop-v1 = member.user_id
                                                  ;[loop-v1 (first (car m))]
                                                  ;Alternative: loop-v1 = member.user.id
                                                  [loop-q (get-content (run (helper-get-member-user-id (third (car m)))))]
                                                  [loop-v1 (first (car (first loop-q)))]
                                                  [loop-v2 (= loop-v1 userid)])
                                                  loop-v2))]
         [loop-br3 (list-recur-with-param loop-br3-func q5 (first current_user))]
         [cond-br3 (and (not (empty? q5)) loop-br3)]
         [br3 (and br2 cond-br3)]
         [untaken-br3 (and br2 (and (not (empty? q5)) (not loop-br3)))]
         ;group_link = ProjectGroupLink.where(:project_id => project.id) // query-project-group-link6
         [q6 (get-content (run (query-project-group-link6 (first project))))]
         [group_link (car (first q6))]
         [group_link-access_level (second group_link)]
         [q7 (get-content (run (query-group-link-groups7 (first project))))]
         [br4 (not (empty? q7))]
         [untaken-br4 (empty? q7)]
         [group_link-groups (car (first q7))]
         ;TODO: Should be range query
         ;mbr = group_link.groups.members.where(:id => current_user.id)
         [q8 (get-content (run (query-group-link-groups-members8 (first group_link-groups) (first current_user))))]
         [cond-br5 (not (empty? q8))]
         [br5 (and br4 cond-br5)]
         [untaken-br5 (and br4 (not cond-br5))]
         [mbr (car (first q8))]
         [acs (first mbr)]
         [cond-br6 (> acs group_link-access_level)]
         [br6 (and br5 cond-br6)]
         [untaken-br6 (and br5 (not cond-br6))]
         ;owner = project.namespace.owner
         [q10 (get-content (run (query-project-namespace-owner10 (first project))))]
         [owner-0 (car (first q10))]
         [local-v1 (get-content (run (query-project-group-members-user11 (first (car (first q5))) (first current_user))))]
         ;; if project.group
         ;;    if project.group.members.user.where(:id => current_user.id)
         [br7 (and br2 (not (empty? local-v1)))]
         [untaken-br7 (and br2 (empty? local-v1))]
         [owner-1 current_user]
         [owner (if br7 owner-1 owner-0)]
         [br8 (not (= (third owner) 0))]
         [untaken-br8 (not br8)]
         [br9 (or (not (second owner)) (fourth project))]
         [untaken-br9 (not br9)]
         [br10 (not (= (fifth project) 0))]
         ;if @project.project_members.where(:access_level => 1)
         [q12 (get-content (run (query-project-project-members-aclevel12 (first project) 1)))]
         [br11 (not (empty? q12))]
         [untaken-br11 (not br11)]
         ;elseif @project.project_members.where(:access_level => 1)
         [q12-2 (get-content (run (query-project-project-members-aclevel12 (first project) 2)))]
         [br12 (and untaken-br11 (not (empty? q12-2)))]
         [untaken-br12 (and untaken-br11 (empty? q12-2))]
         ;events = project.events.exist(:author).limit(20)
         [q13 (get-content (run (query-project-events13 (first project))))]
         [events-count (cdr (first q13))]
         [br13 (= events-count 0)]
         [untaken-br13 (not br13)]
         [loop-br14-func (lambda (e dummy) (
                                     let* ([e-action (first (car e))]
                                           [e-target_id (second (car e))]
                                           [e-target_type (third (car e))]
                                           [loop-v1 (or (= e-action 1) (or (= e-action 2) (= e-action 3)))]
                                           [loop-v2 (or (and (not (= e-target_id 0)) (e-target_type 11)) (or (= e-target_type 12) (= e-target_type 13)))]
                                           [loop-v3 (or loop-v1 loop-v2)])
                                      loop-v3))]
         [loop-br14 (list-recur-with-param loop-br14-func q13 1)]
         [br14 (and (not (empty? q13)) loop-br14)]
         [untaken-br14 (and (not (empty? q13)) (not loop-br14))]
         [q15 (get-content (run (query-user-by-email15 (third ins))))]
         [br15 (not (empty? q15))]
         [untaken-br15 (not br15)]
         )

    ;(and untaken-br1 untaken-br3) ; unsat when user tbl size = 2
    ;untaken-br3
    (and br1 (and br2 (and br3 (and br4 (and br5 (and br6 (and br7
                 (and br8 (and br9 (and br10 (and br11 (and br13 (and br14 (and br15)
                                                                              )))))))))))))
    ;(and br1 (and br2 (and br3 (and br4 (and br6 (and br7 (and br8
    ;                                 (and br9 (and br10 (and br11 br12))))))))))
    
    ;(first (car (first (get-content (run (helper-get-member-user-id (third (car (first q5)))))))))
    ;(first current_user)
    ;(and (not br1) (and br2 (and br3 (and br4 (and br5 (and (not br6)))))))
    ))

;(execute-program (get-symbolic-int-array 3))
(solve (assert (execute-program (get-symbolic-int-array 3))))
