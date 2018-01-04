/**
 * Created by Ryan on 12/1/2015.
 */
public interface CalculatorViewInterface {
    //This method will update the View and display the
    //given String (it will be sent by the model)
    public void display(String val);
    //This method will update the View in order to
    //communicate to the user that he or she has performed an invalid action.
    public void invalid();
}
