#[cfg(test)]
mod tests {
    use petgraph::graph::DiGraph;
    use symbol_table::SymbolTable;

    use crate::automata::{
        action::Action,
        automaton::Automaton,
        edge::Edge,
        expressions::{Comparison, Expression},
        input_enabled::InputEnabled,
        literal::Literal,
        location::Location,
        refinement::Refinement,
        statements::Statement,
    };

    fn new_specification_tioa() -> Automaton {
        let symbols = SymbolTable::new();
        // Location names:
        let waiting_symbol = symbols.intern("waiting");
        let fast_symbol = symbols.intern("fast");
        let slow_symbol = symbols.intern("slow");
        // Action names:
        let grant_symbol = symbols.intern("grant");
        let news_symbol = symbols.intern("grant");

        let clock = 1;

        let grant_action = Action::new(grant_symbol);
        let news_action = Action::new(news_symbol);

        let mut graph = DiGraph::new();
        let waiting_node = graph.add_node(Location::with_name(waiting_symbol));
        let fast_node = graph.add_node(Location::with_name(fast_symbol));
        let slow_node = graph.add_node(Location::new(
            slow_symbol,
            // u <= 20
            Expression::new_clock_constraint(
                Literal::new_clock(clock).into(),
                Comparison::LessThanOrEqual,
                Literal::new_i16(20).into(),
            ),
        ));
        // if u > 2 and grant?
        graph.add_edge(
            waiting_node,
            slow_node,
            Edge::new_input(
                grant_action,
                Expression::new_clock_constraint(
                    Literal::new_clock(clock).into(),
                    Comparison::GreaterThan,
                    Literal::new_i16(2).into(),
                ),
                Statement::empty(),
            ),
        );
        // grant?
        graph.add_edge(
            slow_node,
            slow_node,
            Edge::new_input(grant_action, Literal::new_true().into(), Statement::empty()),
        );
        // news!
        graph.add_edge(
            slow_node,
            slow_node,
            Edge::new_output(news_action, Literal::new_true().into(), Statement::empty()),
        );
        // if u <= 2 and grant? then u := 0
        graph.add_edge(
            waiting_node,
            fast_node,
            Edge::new_input(
                grant_action,
                Expression::new_clock_constraint(
                    Literal::new_clock(clock).into(),
                    Comparison::LessThanOrEqual,
                    Literal::new_i16(2).into(),
                ),
                Statement::FreeClock(clock),
            ),
        );
        // grant?
        graph.add_edge(
            fast_node,
            fast_node,
            Edge::new_input(grant_action, Literal::new_true().into(), Statement::empty()),
        );
        // when news! then u := 0
        graph.add_edge(
            fast_node,
            waiting_node,
            Edge::new_output(
                news_action,
                Literal::new_true().into(),
                Statement::FreeClock(clock),
            ),
        );

        Automaton::new(waiting_node, graph).unwrap()
    }

    #[test]
    fn refinements() {
        let refinment = Refinement::new(
            new_specification_tioa().is_input_enabled().unwrap(),
            new_specification_tioa().is_input_enabled().unwrap(),
        );
        assert!(refinment.is_ok());
        assert!(refinment.unwrap().refines());
    }
}
