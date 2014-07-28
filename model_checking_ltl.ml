open on_the_fly_ltl

let ltl_model_check model formula = is_empty (combined model (on_the_fly_bis (Not formula)));;
