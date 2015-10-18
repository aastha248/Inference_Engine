import java.util.Enumeration;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.ListIterator;

/**
 *
 * @author Aastha
 */
public class check_entailment {
    
    static HashMap<String, Boolean> model_true;
    public LinkedList getsymbols(LogicalExpression knowledge_base, HashMap model)
        {
            LinkedList<symbols> symbol = new LinkedList<symbols>();
            boolean if_present = false;
            for(symbols kb_sml : knowledge_base.symbol)
            {
                if_present = false;
                for(symbols sml : symbol)
                {
                    if(sml.symbol_name.equalsIgnoreCase(kb_sml.symbol_name))
                    {
                        if_present = true;
                        break;
                    }
                } 
                if(if_present == false && !model.containsKey(kb_sml.symbol_name))
                    symbol.add(kb_sml);
            }
            return symbol;
        }
        public boolean TT_Entails(LogicalExpression knowledge_base,LogicalExpression statement, HashMap model)
        {
            model_true = new HashMap<String, Boolean>(model);
           return TT_Check_All(knowledge_base, statement, getsymbols(knowledge_base, model), model);
        }
        public boolean TT_Check_All(LogicalExpression knowledge_base, LogicalExpression statement, LinkedList symbol, HashMap model)
        {
            if(symbol.isEmpty())
            {
                if(PL_True(knowledge_base, model))
                   return PL_True(statement, model);
                else
                {
                    return true;
                }
            }
            else
            {
                
                symbols first = new symbols();
                first = (symbols) symbol.poll();
                HashMap<String, Boolean> temp_model_true = new HashMap<String, Boolean>(model);
                HashMap<String, Boolean> temp_model_false = new HashMap<String, Boolean>(model);
                LinkedList<symbols> temp_list = new LinkedList<symbols>();
                ListIterator<symbols> listIterator = symbol.listIterator();
                while (listIterator.hasNext())
                {
                    temp_list.add(listIterator.next());
                }
                    boolean symbol_true = TT_Check_All(knowledge_base, statement, symbol, Extend(first, true, temp_model_true));
                    symbol = temp_list;
                    boolean symbol_false = TT_Check_All(knowledge_base, statement, symbol, Extend(first, false, temp_model_false));
                    return symbol_true && symbol_false;
            }
        }
        public HashMap Extend(symbols first, boolean value, HashMap model)
        {
            model.put(first.symbol_name, value);
            return model;
        }
        public boolean PL_True(LogicalExpression statement, HashMap model)
        {
            if(statement.getUniqueSymbol() != null)
            {
                String aa = statement.getUniqueSymbol();
                boolean val;
                if(model_true.containsKey(aa))
                    val= (Boolean) model_true.get(aa);
                else
                    val= (Boolean) model.get(aa);
                return val;
            }
            else if(statement.getConnective().equalsIgnoreCase("and"))
            {
                LogicalExpression nextExpression;
                for( Enumeration e = statement.getSubexpressions().elements(); e.hasMoreElements(); ) 
                {
                    nextExpression = ( LogicalExpression )e.nextElement();
                    if (PL_True(nextExpression, model) == false)
                        return false;
                }
                return true;
            }
            else if(statement.getConnective().equalsIgnoreCase("or"))
            {
                LogicalExpression nextExpression;
                for( Enumeration e = statement.getSubexpressions().elements(); e.hasMoreElements(); ) 
                {
                    nextExpression = ( LogicalExpression )e.nextElement();
                    if (PL_True(nextExpression, model) == true)
                        return true;
                }
                return false;
            }
            //to be changed
            else if(statement.getConnective().equalsIgnoreCase("if"))
            {
                LogicalExpression leftExpression, rightExpression;
                boolean left_pl_value = false, right_pl_value = false;
                int count = 0;
                String to_be_true = null;
                for( Enumeration e = statement.getSubexpressions().elements(); e.hasMoreElements(); ) 
                {
                    if(++count == 1)
                    {
                        leftExpression = ( LogicalExpression )e.nextElement();
                        left_pl_value = PL_True(leftExpression, model);
                    }
                    else if(++count >= 2)
                    {
                        rightExpression = ( LogicalExpression )e.nextElement();
                        right_pl_value = PL_True(rightExpression, model);
                    }
                }
                if(left_pl_value == true && right_pl_value == false)
                {
                    if(!model_true.containsKey(to_be_true))
                        model_true.put(to_be_true, left_pl_value);
                        return false;
                }
                return true;
            }
            else if(statement.getConnective().equalsIgnoreCase("iff"))
            {
                LogicalExpression leftExpression, rightExpression;
                boolean left_pl_value = false, right_pl_value = false;
                String to_be_true = null;
                int count = 0;
                for( Enumeration e = statement.getSubexpressions().elements(); e.hasMoreElements(); ) 
                {
                    
                    if(++count == 1)
                    {
                        leftExpression = ( LogicalExpression )e.nextElement();
                        to_be_true = leftExpression.getUniqueSymbol();
                        left_pl_value = PL_True(leftExpression, model);
                    }
                    else if(++count >= 2)
                    {
                        rightExpression = ( LogicalExpression )e.nextElement();
                        right_pl_value = PL_True(rightExpression, model);
                    }
                }
                if(left_pl_value == right_pl_value)
                {
                    if(!model_true.containsKey(to_be_true))
                        model_true.put(to_be_true, left_pl_value);
                    return true;
                }
                return false;
            }
            else if(statement.getConnective().equalsIgnoreCase("not"))
            {
                LogicalExpression nextExpression;
                for( Enumeration e = statement.getSubexpressions().elements(); e.hasMoreElements(); ) 
                {
                    nextExpression = ( LogicalExpression )e.nextElement();
                    if (PL_True(nextExpression, model) == false)
                        return true;
                    
                }
                return false;
            }
            else if(statement.getConnective().equalsIgnoreCase("xor"))
            {
                LogicalExpression nextExpression;
                int count = 0;
                for( Enumeration e = statement.getSubexpressions().elements(); e.hasMoreElements(); ) 
                {
                    nextExpression = ( LogicalExpression )e.nextElement();
                    if (PL_True(nextExpression, model) == true)
                        count++;
                }
                if(count == 1)
                    return true;
                else
                    return false;
            }
            else
                return false;
        }
}
